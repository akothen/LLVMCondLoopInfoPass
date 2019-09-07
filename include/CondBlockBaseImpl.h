//=============== Implementation file for getting a if-blocks forest ================//
//
//=====-------------------------------------------------------------------------=====//
//
// The following class only accounts for "natural" if-else or if-then blocks
// and rare gotos. Loops are treated completely differently and if-headers that
// are loop headers are not taken into account here. To use loops use LoopInfo.h.
//
//=====------------------------------------------------------------------------=====//

#ifndef CONDBLOCKINFOIMPL_H_
#define CONDBLOCKINFOIMPL_H_

#include <memory>
#include <algorithm>
#include <vector>
#include <iostream>
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopInfoImpl.h"
#include "CondBlockBase.h"

using namespace llvm;

// Use this API when it does not matter if the condblocks are pre-ordered or not
template<class BlockT, class CondBlockSetT>
void CondBlockSetBase<BlockT, CondBlockSetT>
::addBlock(const BlockT *block) {
	assert(block && "Error: Cannot had null basic block to the condblockset\n");
	if(block->getTerminator()->getOpcode() == Instruction::Br) {
		assert(block->getTerminator()->getNumSuccessors() != 2
			&& "Error: Add a new condblock set instead of a new block\n");
	}
	CondBlockSetBase<BlockT, CondBlockSetT> *condBlockSet = this;
	while(condBlockSet) {
		condBlockSet->addCondBlock(const_cast<BlockT *>(block));
		condBlockSet = condBlockSet->getParentCondBlockSet();
	}
}

template<class BlockT, class CondBlockSetT>
bool CondBlockSetBase<BlockT, CondBlockSetT>
			::strictlyContainsCondBlockSet(const CondBlockSetT *blockset) const {
// This blockset should contain the header of the given set.
// However, they should not have a common header though.
	if(isCondBlockHeader(blockset->getHeader()))
		return false;

	if(!contains(blockset->Header))
		return false;

// Now we make sure that all blocks in the block set in the
// condblock set.
	std::vector<BlockT *> blockset_blocks = blockset->getCondBlocks();
	typename std::vector<BlockT *>::iterator it = blockset_blocks.begin();
	while(it != blockset_blocks.end()) {
		(*it)->printAsOperand(errs(), false);
		if(!contains(*it))
			return false;
		it++;
	}
	return true;
}

// This is used to add a new sub-condblock set to this condblock set. This
// addition presumes that there was no major change made to the control flow
// graph such that the header, tail or any other block of this condblock set is
// majorly affected. This API assumes that the header and the tail of the new
// sub-condblock set are already set or will be explicitly set after.
template<class BlockT, class CondBlockSetT>
void CondBlockSetBase<BlockT, CondBlockSetT>::
			addSubCondBlockSetToCondBlockSet(CondBlockSetT *newSubCondBlockSet) {
	assert(this != newSubCondBlockSet
			&& "Error: CondBlock set cannot add itself as a sub-condblock set");
	addSubCondBlockSet(newSubCondBlockSet);

// Add the cond blocks of this new sub-condblock sets to the condblocks list of
// this condblock. But make sure that the blocks do not already exist.
	CondBlockSetBase<BlockT, CondBlockSetT> *condBlockSet = this;
	while(condBlockSet) {
	// 	Add head if condblock set does not contain it already
		if(!condBlockSet->contains(newSubCondBlockSet->getHeader())) {
			condBlockSet->addCondBlock(
					const_cast<BlockT *>(newSubCondBlockSet->getHeader()));
		}
		if(newSubCondBlockSet->getCondBlockSetTail()
		&& !condBlockSet->contains(newSubCondBlockSet->getCondBlockSetTail())) {
			condBlockSet->addCondBlock(const_cast<BlockT *>
								(newSubCondBlockSet->getCondBlockSetTail()));
		}
		errs() << "NEW CONDBLOCKS TO BE ADDED\n";
	// Add the new condBlocks
		typename std::vector<BlockT *>::iterator it = (newSubCondBlockSet->getCondBlocks()).begin();
		while(it != (newSubCondBlockSet->getCondBlocks()).end()) {
			if(!condBlockSet->contains(*it)) {
				errs() << "INSIDE\n";
				errs() << "NUM CONDBLOCK SET: "
											<< newSubCondBlockSet->getNumCondBlocksInSet() <<"\n";
				condBlockSet->addCondBlock(*it);
			}
			errs() << "HERE\n";
			it++;
		}
		errs() << "NEW CONDBLOCKS ADDED\n";
		condBlockSet = condBlockSet->getParentCondBlockSet();
	}

// Set this condblock set as the parent
	newSubCondBlockSet->setParentCondBlockSet(this);
}

// B is reachable from A. If any of the successors (not necessarily immediate
// successors) that are pathes to be loop, the path to the loop headers and
// through the loops are ignored. We also do not impose any limits on the number
// of nodes of CFG visited and also we do not consider the loop info in this
// analysis, since the nodes analyzed may have back-edges and can be missterpr-
// -eted to be reachable through the loop. This is how this API is different
// from the similar LLVM's API.
template<class BlockT>
static bool IsPotentiallyReachable(BlockT *A, BlockT *B,
				   const DominatorTreeBase<BlockT, false> &domTree) {
// If basic block ends with an 'unreachable' instruction, no other basic
// block is reached from here.
	if(A->getTerminator()->getOpcode() == Instruction::Unreachable)
		return false;

// When the stop block is unreachable, it's dominated from everywhere,
// regardless of whether there's a path between the two blocks.
	bool dominatorTree = true;
	if(!domTree.isReachableFromEntry(B))
		dominatorTree = false;

// Visit every node of the CFG
	SmallVector<BlockT*, 32> worklist;
	worklist.push_back(A);
	SmallPtrSet<BlockT*, 32> visited;
	while(!worklist.empty()) {
		BlockT *curblock = worklist.pop_back_val();

	// Check if the block has already been previously visited
		if (!visited.insert(curblock).second)
			continue;

	// If basic block ends with an 'unreachable' instruction, no other basic
	// block is reached from here.
		if(curblock->getTerminator()->getOpcode() == Instruction::Unreachable)
			continue;

	// B reached!
		if(curblock == B)
			return true;

	// If any successor block dominates B, path exist to reach it
		if(dominatorTree && domTree.dominates(curblock, B))
			return true;

	// Now we need to check if there is a backedge from the current blocks to
	// any of its successors. So to look for a backedge, the successor has to
	// be a header to a loop with the current basic block being a latch.
		uint64_t index = 0;
		while(index != curblock->getTerminator()->getNumSuccessors()) {
		// Check if the successor dominates the current block
			BlockT *successor = curblock->getTerminator()->getSuccessor(index);
			if(!domTree.dominates(successor, curblock))
				worklist.push_back(successor);
			index++;
		}
	}

// We have exhausted all possible paths and are certain that 'To' can not be
// reached from 'From'.
	return false;
}

// This function is used when it is not clear whether condblocks sets have a tail.
// This function is really useful when the header of condblock sets does not dominate
// a tail. This can happen if there is some other incoming edge to the tail that does
// not come from the condblocks in the condblock sets in question.
template<class BlockT>
static BlockT *FindTail(BlockT *A, BlockT *B,
						const DominatorTreeBase<BlockT, false> &domTree) {
// If basic block ends with an 'unreachable' instruction, no other basic
// block is reached from here.
	if(A->getTerminator()->getOpcode() == Instruction::Unreachable
	|| B->getTerminator()->getOpcode() == Instruction::Unreachable) {
		return nullptr;
	}

// Traverse the control flow graph from one block and see if the nodes being
// traversed are the reachable from the other block.
	SmallVector<BlockT *, 32> worklist;
	worklist.push_back(A);
	SmallPtrSet<BlockT *, 32> visited;
	while(!worklist.empty()) {
		errs() << "LOOP START\n";
		BlockT *curblock = worklist.pop_back_val();

	// Check if the block has already been previously visited
		if (!visited.insert(curblock).second)
			continue;

	// If basic block ends with an 'unreachable' instruction, no other basic
	// block is reached from here.
		if(curblock->getTerminator()->getOpcode() == Instruction::Unreachable)
			continue;

	// Check if the current block has multiple predecessors. If not, then we
	// B can definitely not reach it.
		uint64_t numPreds = 0;
		for(const auto &Pred : children<Inverse<BlockT *>>(curblock)) {
			if(++numPreds == 2) {
			// Check if this node is reachable from block B
				if(IsPotentiallyReachable<BlockT>(B, curblock, domTree))
					return curblock;
				break;
			}
		}

	// Now we need to check if there is a backedge from the current blocks to
	// any of its successors. So to look for a backedge, the successor has to
	// be a header to a loop with the current basic block being a latch.
		uint64_t index = 0;
		while(index != curblock->getTerminator()->getNumSuccessors()) {
		// Check if the successor dominates the current block
			BlockT *successor = curblock->getTerminator()->getSuccessor(index);
			if(!domTree.dominates(successor, curblock))
				worklist.push_back(successor);
			index++;
		}
	}
	return nullptr;
}

template<class BlockT, class CondBlockSetT>
static void BuildCondBlockSet(BlockT *header, BlockT *tail,
							  DomTreeNodeBase<BlockT> *childNode,
							  std::vector<CondBlockSetT *> &condBlockSetVect,
							  const DominatorTreeBase<BlockT, false> &domTree,
							  CondTreeInfoBase<BlockT, CondBlockSetT> *condTreeInfo) {
	//errs() << "++++++++++++++++ BUILDING CONDBLOCK SET +++++++++++++++++++++\n";
// All the children node of this node are in the then block set
	CondBlockSetT *blockSet = condTreeInfo->AllocateCondBlockSet();
	blockSet->setHeader(header);
	std::vector<BlockT *> blockVect;
	errs() << "HEADER OF CONDBLOCK SET: ";
	header->printAsOperand(errs(), false);
	errs() << "\n";
	for(auto childDomNode : post_order(childNode)) {
		childDomNode->getBlock()->printAsOperand(errs(), false);
		blockVect.push_back(childDomNode->getBlock());
	}

// Put the block pointers in the condBlock set. We also map them to the
// condblock set since we discover the inner-most condblock sets first.
	errs() << "BLOCKS IN CONDSET ";
	while(!blockVect.empty()) {
		errs() << " ";
		BlockT *block = blockVect.back();
		block->printAsOperand(errs(), false);
		blockSet->addCondBlock(block);
		blockVect.pop_back();

	// Map the block to condblock set, if not  done already
		if(!condTreeInfo->getCondBlockSetFor(block))
			condTreeInfo->addToMap(blockSet, block);
	}
	errs() << "\n";
	blockSet->setTail(tail);
	blockSet->printSubCondBlockSets();

// Look for the blocksets from the conddblockset std::vector
	if(!condBlockSetVect.empty()) {
	// Check which of the given blocksets are subsets of the current blockset and
	// check which blocksets have the current blocksets as parent and see if a pair
	// is found, if it is, add it to the pair dense map.
		typename std::vector<CondBlockSetT *>::iterator set_it = condBlockSetVect.begin();
		while(set_it != condBlockSetVect.end()) {
		// Has a pair been found
			if(!condTreeInfo->getPartnerCondBlockSet(*set_it)) {
			// If headers match, condblock sets are a pair
				if((*set_it)->getHeader() == blockSet->getHeader()) {
					condTreeInfo->addCondBlockSetPair(blockSet, *set_it);
					condTreeInfo->addCondBlockSetPair(*set_it, blockSet);
				}
			}

		// Is it a parent?
			if(blockSet->strictlyContainsCondBlockSet(*set_it)) {
			// Check if the parent of this blockset has been found. If not, blockSet
			// is the parent since the order in which the dominator tree is traversed
			// is in post-order, so children are analyzed before their parents.
				if(!(*set_it)->getParentCondBlockSet()) {
					(*set_it)->setParentCondBlockSet(blockSet);
					//(*set_it)->printCondBlockSetInfo();

				// Now the blockset pointed to by the iterator is the sub-blockset to
				// the current blockset.
					blockSet->addSubCondBlockSet(*set_it);
				}
			}
			set_it++;
		}
	}

// Make sure that the subcondblockets are pre-ordered
	blockSet->preorderSubCondBlockSets(domTree);

// Add the block set to the std::vector to track the sub-block sets
	condBlockSetVect.push_back(blockSet);
	//blockSet->printSubCondBlockSetsInSet();
	//errs() << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++=\n";
}


// **** IMPORTANT: Head does NOT have to dominate the tail or any condblocks ******
template<class BlockT, class CondBlockSetT>
static void FindingCondBlockSets(BlockT *potentialHeader,
								 std::vector<CondBlockSetT *> &condBlockSetVect,
								 const DominatorTreeBase<BlockT, false> &domTree,
								 CondTreeInfoBase<BlockT, CondBlockSetT> *condTreeInfo) {
// Check to see if it is a triangle case. See if one successor is reachable from the other.
	auto *cond_branch = potentialHeader->getTerminator();
	errs() << "COND BRANCH: ";
	cond_branch->print(errs());
	errs() << "\n";
	bool reachable = IsPotentiallyReachable<BlockT>(cond_branch->getSuccessor(0),
													cond_branch->getSuccessor(1), domTree);
	if(reachable == false) {
	// Switch the successors around
		reachable = IsPotentiallyReachable<BlockT>(cond_branch->getSuccessor(1),
												   cond_branch->getSuccessor(0), domTree);
		if(reachable == false) {
		// Try to find a tail, if possible. It is possible a tail exists but
		// the potential header does not dominate the tail and there are
		// multiple edges pointing into the tail. So first thing we need to
		// do is to try to find the tail first.
			BlockT *tailBlock = FindTail<BlockT>(cond_branch->getSuccessor(0),
										 cond_branch->getSuccessor(1), domTree);
			errs() << "TAIL BLOCK FOUND: ";
			if(tailBlock) {
				tailBlock->printAsOperand(errs(), false);
			} else {
				errs() << "NONE";
			}
			errs() << "\n";

			errs() << "SUCCESSOR 0\n";
			cond_branch->getSuccessor(0)->printAsOperand(errs(), false);
			errs() << "\n";
			DomTreeNodeBase<BlockT> *childNode = domTree.getNode(cond_branch->getSuccessor(0));
			BuildCondBlockSet<BlockT, CondBlockSetT>(potentialHeader, tailBlock,
									childNode, condBlockSetVect, domTree, condTreeInfo);

			errs() << "SUCCESSOR 1\n";
			cond_branch->getSuccessor(1)->printAsOperand(errs(), false);
			errs() << "\n";
			childNode = domTree.getNode(cond_branch->getSuccessor(1));
			BuildCondBlockSet<BlockT, CondBlockSetT>(potentialHeader, tailBlock,
									childNode, condBlockSetVect, domTree, condTreeInfo);
			return;
		}

	// Successor 0 reachable  from 1
		errs() << "Edge from ";
		cond_branch->getSuccessor(1)->printAsOperand(errs(), false);
		errs() << " to ";
		cond_branch->getSuccessor(0)->printAsOperand(errs(), false);
		errs() << "\n";
		BlockT *tailBlock = cond_branch->getSuccessor(0);
		DomTreeNodeBase<BlockT> *childNode = domTree.getNode(cond_branch->getSuccessor(1));
		BuildCondBlockSet<BlockT, CondBlockSetT>(potentialHeader, tailBlock,
									childNode, condBlockSetVect, domTree, condTreeInfo);
		return;
	}

// Successor 1 reachable  from 0
	errs() << "Edge from ";
	cond_branch->getSuccessor(0)->printAsOperand(errs(), false);
	errs() << " to ";
	cond_branch->getSuccessor(1)->printAsOperand(errs(), false);
	errs() << "\n";
	BlockT *tailBlock = cond_branch->getSuccessor(1);
	DomTreeNodeBase<BlockT> *childNode = domTree.getNode(cond_branch->getSuccessor(0));
	BuildCondBlockSet<BlockT, CondBlockSetT>(potentialHeader, tailBlock,
								childNode, condBlockSetVect, domTree, condTreeInfo);
}

// This is used to compute the condInfo forest. The exit blocks of the loops are
// treated as the headers of the condblock sets. The main requirement for the
// condblock sets is that the header always dominates the blocks in the condblock
// sets. Most of the 'natural' condblock sets get found. However, we tend to
// miss out on cases as one below:
//
//						    A
//						   /|
//						  B |
//						 / \|
//						D   C
//						 \  |
//              		  \ |
//						   \|
//						    E
//
// In the above example, A dominates B,D,C and E. We can clearly see two
// condblock sets with the tail E: A, B, D, E and A, C, E. However, condblocks
// sets of B, C, E and B, D and E remain undetected since B does not dominate C
// but it does dominate D. B does not dominate E.
// FIXME: Cases like above need to be detected for the sake completeness.
// UPDATED STATUS: Above problem probably fixed. Solution: The condblock sets
// should not have to be dominated by the header.
template<class BlockT, class CondBlockSetT>
void CondTreeInfoBase<BlockT, CondBlockSetT>
			::analyze(const DominatorTreeBase<BlockT, false> &domTree) {
	std::vector<CondBlockSetT *> condBlockSetVect;
	const DomTreeNodeBase<BlockT> *domRoot = domTree.getRootNode();
	for(auto domNode : post_order(domRoot)) {
		BlockT *potentialHeader = domNode->getBlock();
		//errs() << "POTENTIAL HEADER ";
		//potentialHeader->printAsOperand(errs(), false);
		//errs() << "\n";

	// The terminator must be a branch or else move on to some other block
		auto *term_inst = potentialHeader->getTerminator();
		if(term_inst->getOpcode() != Instruction::Br)
			continue;

		if(term_inst->getNumSuccessors() != 2)
			continue;

	// The potential header must be reachable from entry
		if(!domTree.isReachableFromEntry(potentialHeader))
			continue;

	// POTENTIAL INCOMPLETE CONDSET CASE: It is possible that one of the branches
	// goes to a block that dominates the potential header or the successor is not
	// dominated by the potential header because of some other incoming edge.
	// In this case, the potential  header will dominate only one child. There
	// MIGHT BE A TAIL.
		if(domNode->getNumChildren() < 2) {
			errs() << "DOM TREE NUMBER OF CHILDREN == 0 or 1\n";
			errs() << "POTENTIAL HEADER: ";
			potentialHeader->printAsOperand(errs(), false);
			errs() << "\n";
			//tailBlock = nullptr;
			if(!domTree.dominates(term_inst->getSuccessor(0), potentialHeader)
			&& !domTree.dominates(term_inst->getSuccessor(1), potentialHeader)) {
				FindingCondBlockSets<BlockT, CondBlockSetT>
							(potentialHeader, condBlockSetVect, domTree, this);
			}
			continue;
		}

	// POTENTIAL TRIANGLE CASE: Now we get the tail of the condblock set. The
	// header is expected to have three children tops. If there are only two
	// children, then one of the successors should be the tail.
		if(domNode->getNumChildren() == 2) {
			errs() << "DOM TREE NUMBER OF CHILDREN == 2\n";
			FindingCondBlockSets<BlockT, CondBlockSetT>
							(potentialHeader, condBlockSetVect, domTree, this);
			continue;
		}

	// POTENTIAL DIAMOND CASE: There is one tail.
		if(domNode->getNumChildren() == 3) {
			errs() << "DOM TREE NUMBER OF CHILDREN == 3\n";
		// Find the node corresponding to the tail
			size_t index = 0;
			while(index != domNode->getNumChildren()) {
				if(term_inst->getSuccessor(0) != (domNode->getChildren()[index])->getBlock()
				&& term_inst->getSuccessor(1) != (domNode->getChildren()[index])->getBlock()) {
					BlockT *tailBlock = (domNode->getChildren()[index])->getBlock();

				// Build two condblock sets
					DomTreeNodeBase<BlockT> *childNode = domTree.getNode(term_inst->getSuccessor(0));
					assert(childNode && tailBlock && "Error in Dominator Tree\n");
					BuildCondBlockSet<BlockT, CondBlockSetT>(potentialHeader, tailBlock,
												childNode, condBlockSetVect, domTree, this);

					childNode = domTree.getNode(term_inst->getSuccessor(1));
					assert(childNode && tailBlock && "Error in Dominator Tree\n");
					BuildCondBlockSet<BlockT, CondBlockSetT>(potentialHeader, tailBlock,
													childNode, condBlockSetVect, domTree, this);
				}
				index++;
			}
			continue;
		}
		assert("Error in dominator tree: more children in header than required\n");
	}

// Now, we discover all the top-level condblocks by checking whether they have
// a parent or not and std::map blocks with the inner-most condBlocksets.
	errs() << "TOP LEVEL ADD\n";
	typename std::vector<CondBlockSetT *>::iterator set_it = condBlockSetVect.begin();
	while(set_it != condBlockSetVect.end()) {
		if(!(*set_it)->getParentCondBlockSet()) {
		// Since there is no parent, it is a top-level condBlockSet
			addTopLevelCondBlockSet(*set_it);
		}
		set_it++;
	}

// Now, we pre-order the top-level condblocksets
	preorderTopLevelCondBlockSets(domTree);
	//printTopLevelCondBlockSets();
	printTopLevelCondBlockSets();
}

template<class BlockT, class CondBlockSetT>
void CondTreeInfoBase<BlockT, CondBlockSetT>
	  ::addTopLevelCondBlockSet(CondBlockSetT *blockSet,
								const DominatorTreeBase<BlockT, false> &domTree) {
	errs() << "ADDING TOP LEVEL CONDBLOCK SET\n";
	assert(blockSet && "Error: Cannot add a null top-level conblock set\n");

// Map tails to the head of the condblock set
	if(blockSet->getTail()) {
		errs() << "TOP LEVEL TAIL: ";
		blockSet->getTail()->printAsOperand(errs(), false);
		errs() << "\n";
		if(const BlockT *tail = blockSet->getTail()) {
			TopLevelTailsToHeadsMap[tail] = const_cast<BlockT *>(blockSet->getHeader());
			errs() << "TAIL MAPPED\n";
		}
	}

// Append the given blockset into the top-level condblock set into the vector and
// maintain the order form of the vector.
	TopLevelCondBlockSets.push_back(blockSet);
	preorderTopLevelCondBlockSets(domTree);
	typename std::vector<CondBlockSetT *>::iterator it = TopLevelCondBlockSets.begin();
	while(it != TopLevelCondBlockSets.end()) {
		if(domTree.properlyDominates(blockSet->getHeader(), (*it)->getHeader())) {
		// We need to insert this block into the vector
			std::vector<CondBlockSetT *> vect;
			vect.reserve(TopLevelCondBlockSets.size());
			std::copy(TopLevelCondBlockSets.begin(), it, vect.begin());
			vect.push_back(blockSet);
			std::copy(it, TopLevelCondBlockSets.end(), vect.end());
			break;
		}
		it++;
	}
}

template<class BlockT, class CondBlockSetT>
void CondTreeInfoBase<BlockT, CondBlockSetT>
::preorderTopLevelCondBlockSets(const DominatorTreeBase<BlockT, false> &domTree) {
	typename std::vector<CondBlockSetT *>::iterator condBlockSet_it =
										TopLevelCondBlockSets.begin();
	while(condBlockSet_it != TopLevelCondBlockSets.end()) {
		typename std::vector<CondBlockSetT *>::iterator check_it = condBlockSet_it + 1;
		const BlockT *condBlockSetHeader = (*condBlockSet_it)->getHeader();
		while(check_it != TopLevelCondBlockSets.end()) {
			if(check_it != condBlockSet_it) {
				const BlockT *check_header = (*check_it)->getHeader();
				if(domTree.dominates(domTree.getNode(const_cast<BlockT *>(check_header)),
						     domTree.getNode(const_cast<BlockT *>(condBlockSetHeader)))) {
				// Now we need to swap elements
					CondBlockSetT *temp = *check_it;
					*check_it = *condBlockSet_it;
					*condBlockSet_it = temp;
				}
			}
			check_it++;
		}
		condBlockSet_it++;
	}
}

template<class BlockT, class CondBlockSetT>
void CondBlockSetBase<BlockT, CondBlockSetT>
			::preorderSubCondBlockSets(const DominatorTreeBase<BlockT, false> &domTree) {
	typename std::vector<CondBlockSetT *>::iterator condBlockSet_it = SubCondBlockSets.begin();
	while(condBlockSet_it != SubCondBlockSets.end()) {
		typename std::vector<CondBlockSetT *>::iterator check_it = condBlockSet_it + 1;
		const BlockT *condBlockSetHeader = (*condBlockSet_it)->getHeader();
		while(check_it != SubCondBlockSets.end()) {
			const BlockT *check_header = (*check_it)->getHeader();
			if(domTree.dominates(domTree.getNode(const_cast<BlockT *>(check_header)),
						 domTree.getNode(const_cast<BlockT *>(condBlockSetHeader)))) {
			// Now we need to swap elements
				CondBlockSetT *temp = *check_it;
				*check_it = *condBlockSet_it;
				*condBlockSet_it = temp;
			}
			check_it++;
		}
		condBlockSet_it++;
	}
}

template<class BlockT, class CondBlockSetT>
void CondTreeInfoBase<BlockT, CondBlockSetT>
::postorderTopLevelCondBlockSets(const DominatorTreeBase<BlockT, false> &domTree) {
// Make sure that the top-level condBlocks are pre-ordered first
	preorderTopLevelCondBlockSets(domTree);

// Reverse the order of the std::vector now
	std::vector<CondBlockSetT *> postOrderCondBlockSets;
	typename std::vector<CondBlockSetT *>::reverse_iterator vect_it =
										TopLevelCondBlockSets.rbegin();
	while(vect_it != TopLevelCondBlockSets.rend()) {
		postOrderCondBlockSets.push_back(*vect_it);
		vect_it++;
	}
	TopLevelCondBlockSets = postOrderCondBlockSets;
}

template<class BlockT, class CondBlockSetT>
CondBlockSetT *CondTreeInfoBase<BlockT, CondBlockSetT>
::getCondBlockSetForHeader(const BlockT *potentialHeader) const {
// In order for a block to be a condblock set header, it needs to have a
// terminator with exactly two successors in CFG.
	assert(potentialHeader && "Error: Condblock header cannot be null\n");

	if(potentialHeader->getTerminator()->getOpcode() != Instruction::Br)
		return nullptr;
	if(potentialHeader->getTerminator()->getNumSuccessors() != 2)
		return nullptr;

// Okay, this is potentially a header but the only way to ascertain this is by
// walking down the condtree and checking if any of the existing condblock sets
// have this block as a header. The quickest way to start would be to get the
// condblock set that might contain the potential header first. If it does not
// exist, then we could do it exhaustively by starting from the  top-level
// condBlock sets first.
	SmallVector<CondBlockSetT *, 8> condBlockSetWorklist;
	if(CondBlockSetBlockMap.lookup(potentialHeader)) {
	// Inner-most condblock set for this potential  header exists.
	// Just check all  sub-condblock sets.
		std::vector<CondBlockSetT *> subCondBlockSetVect =
				CondBlockSetBlockMap.lookup(potentialHeader)->getSubCondBlockSets();
		condBlockSetWorklist.append(subCondBlockSetVect.begin(), subCondBlockSetVect.end());
		while(!condBlockSetWorklist.empty()) {
			CondBlockSetT *condBlockSet = condBlockSetWorklist.back();
			condBlockSetWorklist.pop_back();
			if(condBlockSet->getHeader() == potentialHeader)
				return condBlockSet;
		}
	} else {
		condBlockSetWorklist.append(TopLevelCondBlockSets.begin(), TopLevelCondBlockSets.end());
		while(!condBlockSetWorklist.empty()) {
			CondBlockSetT *condBlockSet = condBlockSetWorklist.back();
			condBlockSetWorklist.pop_back();
			if(condBlockSet->getHeader() == potentialHeader)
				return condBlockSet;
			std::vector<CondBlockSetT *> condBlockSetVect = condBlockSet->getSubCondBlockSets();
			condBlockSetWorklist.append(condBlockSetVect.begin(),condBlockSetVect.end());
		}
	}
	return nullptr;
}

template<class BlockT, class CondBlockSetT>
bool CondTreeInfoBase<BlockT, CondBlockSetT>
::isCondBlockSetTail(const BlockT *potentialTail) const {
// The only way to ascertain this is a potential tail is by walking down the condtree
// and checking if any of the existing condblock sets have this block as a header.
	SmallVector<CondBlockSetT *, 8> condBlockSetWorklist;
	condBlockSetWorklist.append(TopLevelCondBlockSets.begin(), TopLevelCondBlockSets.end());
	while(!condBlockSetWorklist.empty()) {
		CondBlockSetT *condBlockSet = condBlockSetWorklist.back();
		condBlockSetWorklist.pop_back();
		if(condBlockSet->getTail() == potentialTail)
			return true;
		condBlockSetWorklist.append(condBlockSet->begin(), condBlockSet->end());
	}
	return false;
}

template<class BlockT, class CondBlockSetT>
std::vector<CondBlockSetT *>
CondTreeInfoBase<BlockT, CondBlockSetT>::getCondBlockSetsInPreorder()  {
// Iterate over the top-level condblock sets and then descend into the
// sub-condblocksets and put them in the vector as we go. The top-level nodes
// and sub-condblock sets are all pre-ordered.
	std::vector<CondBlockSetT *> preorderCondBlockSets;
	SmallVector<CondBlockSetT *, 4> preorderWorklist;
	iterator it = begin();
	while(it != end()) {
		CondBlockSetT *topLevelCondBlockSet = *it;
		preorderWorklist.push_back(topLevelCondBlockSet);
		while(!preorderWorklist.empty()) {
			CondBlockSetT *condBlockSet = preorderWorklist.pop_back_val();
			preorderWorklist.append(condBlockSet->begin(), condBlockSet->end());
			preorderCondBlockSets.push_back(condBlockSet);
		}
		it++;
	}
	//printCondBlockSetsVector(preorderCondBlockSets);
	//errs() << "PREORDER CONDBLOCK SETS VECTOR LENGTH:" << preorderCondBlockSets.size() << "\n";
	return preorderCondBlockSets;
}

#endif
