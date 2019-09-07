//=============== Header file for getting a if-blocks forest ================//
//
//=====------------------------------------------------------------------=====//
//
// The following classes accounts for "natural" if-else or if-then blocks
// and rare gotos. Loops are treated completely differently and if-headers that
// are loop headers are not taken into account here. To use loops use LoopInfo.h.
// Also, cond loops are implemented here. Cond Loops are, again, "natural" loops,
// that are also hold info on cond block sets along with the other loop info in
// LLVM LoopInfoBase and LoopBase.
//
//=====------------------------------------------------------------------=====//

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
#include "GenCondInfo.h"
#include "CondBlockBaseImpl.h"

using namespace llvm;

template <class BlockT, class LoopT, class CondBlockSetT>
void GenCondBlockSetBase<BlockT, LoopT, CondBlockSetT>
				::preorderSubLoops(const DominatorTreeBase<BlockT, false> &domTree) {
	loop_iterator loop_it = loop_begin();
	while(loop_it != loop_end()) {
		loop_iterator check_it = loop_it + 1;
		const BlockT *loopHeader = (*loop_it)->getHeader();
		while(check_it != loop_end()) {
			if(check_it != loop_it) {
				const BlockT *check_header = (*check_it)->getHeader();
				if(domTree.dominates(domTree.getNode(const_cast<BlockT *>(check_header)),
							 domTree.getNode(const_cast<BlockT *>(loopHeader)))) {
				// Now we need to swap elements
					LoopT *temp = *check_it;
					*check_it = *loop_it;
					*loop_it = temp;
				}
			}
			check_it++;
		}
		loop_it++;
	}
}

template <class BlockT, class LoopT, class CondBlockSetT>
void GenCondBlockSetBase<BlockT, LoopT, CondBlockSetT>
		::postorderSubLoops(const DominatorTreeBase<BlockT, false> &domTree) {
// Make sure that the top-level condBlocks are pre-ordered first
	preorderSubLoops(domTree);

// Reverse the order of the std::vector now
	std::vector<LoopT *> postOrderLoops;
	reverse_loop_iterator vect_it = loop_rbegin();
	while(vect_it != loop_rend()) {
		postOrderLoops.push_back(*vect_it);
		vect_it++;
	}
	SubLoops = postOrderLoops;
}

template <class BlockT, class LoopT, class CondBlockSetT>
void GenCondBlockSetLoopInfoBase<BlockT, LoopT, CondBlockSetT>
	::bindCondBlockSetTreeToLoopTree(const DominatorTreeBase<BlockT, false> &domTree) {
	errs() << "\n\n\n\n*********** BUILDING CONDBLOCKSET INFO IN CONDLOOP *************\n";
// Get the condloops in a pre-ordered vector
	SmallVector<LoopT *, 4> condLoopsSmallVect =
									LoopInfoBase<BlockT, LoopT>::getLoopsInPreorder();
	std::vector<LoopT *> temp_condLoopsVect;
	while(!condLoopsSmallVect.empty()) {
		LoopT *loop = condLoopsSmallVect.pop_back_val();
		temp_condLoopsVect.push_back(loop);
	}

//  Reverse the order of the loops in the vector
	std::vector<LoopT *> condLoopsVect;
	while(!temp_condLoopsVect.empty()) {
		condLoopsVect.push_back(temp_condLoopsVect.back());
		temp_condLoopsVect.pop_back();
	}

// Get the parent condblock set. We define parent condblock set as a condblock
// set that includes all the loop blocks in a condblock set.
	typename std::vector<LoopT *>::iterator loop = condLoopsVect.begin();
	while(loop != condLoopsVect.end()) {
		std::vector<BlockT *> loopBlocks = (*loop)->getBlocksVector();

	// Set the parent condBlock set
		CondBlockSetT *parentCondBlockSet =
				const_cast<CondBlockSetT *>(CondTreeInfoBase<BlockT, CondBlockSetT>
												::getCondBlockSetFor((*loop)->getHeader()));
		//errs() << "LOOP HEADER: ";
		//((*condLoop)->getHeader())->printAsOperand(errs(), false);
		//errs() << "\n";
		(*loop)->setParentCondBlockSet(parentCondBlockSet);
		//errs() << "INITIAL PARENT CONDBLOCK SET\n";
		//if(!parentCondBlockSet)
			//errs() << "PARENT CONDBLOCK SET IS NULL\n";
		//else
			//parentCondBlockSet->printCondBlocksInSet();
		typename std::vector<BlockT *>::iterator block = loopBlocks.begin();
		while(block != loopBlocks.end()) {
		// If the block is in the parent loop, then we continue, or else there is
		// no parent loop for the condblock set in question.
			if(!parentCondBlockSet)
				break;
			if(!parentCondBlockSet->contains(*block)) {
				parentCondBlockSet =
						const_cast<CondBlockSetT *>(
									parentCondBlockSet->getParentCondBlockSet());
				(*loop)->setParentCondBlockSet(parentCondBlockSet);
				block = loopBlocks.begin();
				continue;
			}
			block++;
		}
		//if(parentCondBlockSet) {
			//errs() << "PARENT CONDBLOCK SET: ";
			//parentCondBlockSet->printCondBlocksInSet();
			//errs() << "\n";
		//} else {
			//errs() << "NO PARENT CONDBLOCK SET\n";
		//}

	// Find out the sub-condblock sets in this condloop by reverse traversing the CFG
		const BlockT *header = (*loop)->getHeader();
		block = loopBlocks.begin();
		while(block != loopBlocks.end()) {
		// Put the potential sub-condblock sets in a worklist from inner-most to
		// outer-most condblock sets.
			std::vector<CondBlockSetT *> subCondBlocksWorklist;
			CondBlockSetT *subCondBlockSet =
					const_cast<CondBlockSetT *>(this->getCondBlockSetFor(*block));
			//errs() << "BLOCK CONSIDERED: ";
			//if(!*block)
				//errs() << "NULL";
			//else
				//(*block)->printAsOperand(errs(), false);
			//errs() << "\n";
			//if(!subCondBlockSet) {
				//errs() << "SUBCONDBLOCK SET IS NULL\n";
			//} else {
				//errs() << "SUBCONDBLOCK TO CONSIDER SET INFO: \n";
				//subCondBlockSet->printCondBlocksInSet();
			//}
			while(subCondBlockSet
			   && domTree.dominates(header, subCondBlockSet->getHeader())
			   && (*loop)->getNumBlocks() >= subCondBlockSet->getNumCondBlocks()) {
				if(find(subCondBlocksWorklist.begin(), subCondBlocksWorklist.end(),
											subCondBlockSet) == subCondBlocksWorklist.end()) {
					//errs() << "PUT SUBCONDBLOCKSET IN WORKLIST\n";
					//subCondBlockSet->printCondBlocksInSet();
					subCondBlocksWorklist.push_back(subCondBlockSet);
				}
				subCondBlockSet = const_cast<CondBlockSetT *>(
										subCondBlockSet->getParentCondBlockSet());
				//if(!subCondBlockSet) {
					//errs() << "SUBCONDBLOCK SET IS NULL\n";
				//} else {
					//errs() << "SUBCONDBLOCK TO CONSIDER SET INFO: \n";
					//subCondBlockSet->printCondBlocksInSet();
				//}
			}

			while(!subCondBlocksWorklist.empty()) {
			// Now we reverse iterate over the worklist and see which sub-condblock
			// set is actually lies completely inside a loop.
				subCondBlockSet = subCondBlocksWorklist.back();
				subCondBlocksWorklist.pop_back();

			// If the sub-condblock set happens to be the discovered parent condblock
			// set, we continue.
				if((*loop)->getParentCondBlockSet() == subCondBlockSet)
					continue;

			// Iterate over every block in the condblock and make sure that all blocks
			// lie in the loop.
				typename CondBlockSetBase<BlockT, CondBlockSetT>::block_iterator
								blockInCondBlockSet = subCondBlockSet->block_begin();
				while(blockInCondBlockSet != subCondBlockSet->block_end()) {
					if(!(*loop)->contains(*blockInCondBlockSet))
						goto next_subCondBlockSet;
					blockInCondBlockSet++;
				}

			// This means that a subloop has been found, put it into the subloop vector
			// for this condblock set if it has not been already.
				if(!(*loop)->containsSubCondBlockSet(subCondBlockSet)) {
					//errs() << "SUBCOND BLOCK SET ADDED: \n";
					//subCondBlockSet->printCondBlocksInSet();
					(*loop)->addSubCondBlockSet(subCondBlockSet);
				}
				//errs() << "BREAK\n";
				break;

			next_subCondBlockSet:  // Keep the compiler happy
				continue;
			}
			block++;
		}
		//errs() << "\n\n";
		//errs() << "--------------------------------------------------------------------------\n";
		//(*condLoop)->printCondLoopInfo();
		//(*condLoop)->printCondBlockSetInfo();
		//errs() << "\n\n";
		loop++;
	}
	errs() << "*****************************************************************************\n";
}

template <class BlockT, class LoopT, class CondBlockSetT>
void GenCondBlockSetLoopInfoBase<BlockT, LoopT, CondBlockSetT>
::bindLoopTreeToCondBlockSetTree(const DominatorTreeBase<BlockT, false> &domTree) {
// Get the condblock sets in a pre-ordered vector
	std::vector<CondBlockSetT *> condBlockSetsVect = getCondBlockSetsInPreorder();

// Get the parent loop. We define parent loop as a loop that includes all the blocks
// in a common loop.
	typename std::vector<CondBlockSetT *>::iterator condBlockSet = condBlockSetsVect.begin();
	while(condBlockSet != condBlockSetsVect.end()) {
		std::vector<BlockT *> condBlocks = (*condBlockSet)->getCondBlocks();

	// Set the parent loop
		LoopT *parentLoop = getLoopFor((*condBlockSet)->getHeader());
		(*condBlockSet)->setParentLoop(parentLoop);
		typename CondBlockSetBase<BlockT, CondBlockSetT>::block_iterator block =
													(*condBlockSet)->block_begin();
		while(block != (*condBlockSet)->block_end()) {
		// If the block is in the parent loop, then we continue, or else there is
		// no parent loop for the condblock set in question.
			if(!parentLoop)
				break;
			if(!parentLoop->contains(*block)) {
				parentLoop = parentLoop->getParentLoop();
				(*condBlockSet)->setParentLoop(parentLoop);
				block = condBlocks.begin();
				continue;
			}
			block++;
		}

		//(*condBlockSet)->printParentLoop();

	// Find out the sub-loops in this condblock set by reverse traversing the CFG
		const BlockT *header = (*condBlockSet)->getHeader();
		block = condBlocks.begin();
		while(block != condBlocks.end()) {
		// Put the potential subloops in a worklist from inner-most to outer-most loops
			std::vector<LoopT *> subLoopWorklist;
			LoopT *subloop = getLoopFor(*block);
			while(subloop && domTree.properlyDominates(header, subloop->getHeader())) {
				if(find(subLoopWorklist.begin(), subLoopWorklist.end(),
											subloop) == subLoopWorklist.end()) {
					subLoopWorklist.push_back(subloop);
				}
				subloop = subloop->getParentLoop();
			}

			while(!subLoopWorklist.empty()) {
			// Now we reverse iterate over the worklist and see which subloop is
			// actually lies completely inside a condblock set.
				subloop = subLoopWorklist.back();
				subLoopWorklist.pop_back();

			// If the subloop happens to be the discovered parent loop, we continue
				if((*condBlockSet)->getParentLoop() == subloop)
					continue;

			// Iterate over every block in the loop and make sure that all blocks
			// lie in the condblock set.
				typename std::vector<BlockT *>::const_iterator blockInLoop =
										(subloop->getBlocksVector()).begin();
				while(blockInLoop != (subloop->getBlocksVector()).end()) {
					if(!(*condBlockSet)->contains(*blockInLoop))
						goto next_subloop;
					blockInLoop++;
				}

			// This means that a subloop has been found, put it into the subloop vector
			// for this condblock set if it has been already.
				if(!(*condBlockSet)->containsSubLoop(subloop))
					(*condBlockSet)->addSubLoop(subloop);
				break;

			next_subloop:  // Keep the compiler happy
				continue;
			}
			block++;
		}
		//errs() << "\n\n";
		//errs() << "--------------------------------------------------------------------------\n";
		//(*condBlockSet)->printCondBlockSetInfo();
		//(*condBlockSet)->printLoopInfo();
		//errs() << "\n\n";
		condBlockSet++;
	}
}

/*
template <class BlockT, class LoopT, class CondBlockSetT>
static std::vector<GenLoopBase<BlockT, LoopT, CondBlockSetT> *>
GetLoopsInPreorder(const CondLoopTreeInfo *condLoopTreeInfo)
{
	std::vector<LoopBase<BasicBlock, CondLoop> *> preorderedLoops;
	SmallVector<LoopBase<BasicBlock, CondLoop> *, 4> preorderWorklist;
	LoopInfoBase<BasicBlock, CondLoop>::reverse_iterator loop_it =
															condLoopTreeInfo->rbegin();
	while (loop_it != condLoopTreeInfo->rend()) {
		preorderWorklist.push_back(*loop_it);
		while(!preorderWorklist.empty()) {
		// Sub-loops are stored in forward program order, but will process the
		// worklist backwards so append them in reverse order.
			LoopBase<BasicBlock, CondLoop> *loop = preorderWorklist.pop_back_val();
			preorderWorklist.append(loop->rbegin(), loop->rend());
			preorderedLoops.push_back(loop);
		}
		loop_it++;
	}
	return preorderedLoops;
}
*/
template <class BlockT, class LoopT, class CondBlockSetT>
void GenLoopBase<BlockT, LoopT, CondBlockSetT>
		::preorderSubCondBlockSets(const DominatorTreeBase<BlockT, false> &domTree) {
	condblockset_iterator condBlockSet_it = condblockset_begin();
	while(condBlockSet_it != condblockset_end()) {
		condblockset_iterator check_it = condBlockSet_it + 1;
		const BasicBlock *condBlockSetHeader = (*condBlockSet_it)->getHeader();
		while(check_it != condblockset_end()) {
			if(check_it != condBlockSet_it) {
				const BasicBlock *check_header = (*check_it)->getHeader();
				if(domTree.dominates(domTree.getNode(
									const_cast<BasicBlock *>(check_header)),
							 domTree.getNode(const_cast<BasicBlock *>(condBlockSetHeader)))) {
				// Now we need to swap elements
					CondBlockSet *temp = *check_it;
					*check_it = *condBlockSet_it;
					*condBlockSet_it = temp;
				}
			}
			check_it++;
		}
		condBlockSet_it++;
	}
}

template<class BlockT, class LoopT, class CondBlockSetT>
void GenLoopBase<BlockT, LoopT, CondBlockSetT>
::postorderSubCondBlockSets(const DominatorTreeBase<BlockT, false> &domTree) {
// Make sure that the top-level condBlocks are pre-ordered first
	preorderSubCondBlockSets(domTree);

// Reverse the order of the std::vector now
	std::vector<CondBlockSetT *> postorderCondBlockSets;
	reverse_condblockset_iterator vect_it = condblockset_rbegin();
	while(vect_it != condblockset_rend()) {
		postorderCondBlockSets.push_back(*vect_it);
		vect_it++;
	}
	SubCondBlockSets = postorderCondBlockSets;
}


//====---------------------------------------------------------------------===//
// GenCondInfoWrapperPass Info

char GenCondBlockSetLoopInfoWrapperPass::ID = 0;
char GenCondBlockSetLoopInfoPass::ID = 0;

static RegisterPass<GenCondBlockSetLoopInfoPass> PassObj("General CondInfo Pass",
																													"Run GenCondInfo Pass");

INITIALIZE_PASS_BEGIN(GenCondBlockSetLoopInfoWrapperPass,
					"genInfo", "Natural Loop Information", true, true)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(GenCondBlockSetLoopInfoWrapperPass,
					"genInfo", "Natural Loop Information", true, true)

bool GenCondBlockSetLoopInfoWrapperPass::runOnFunction(Function &) {
	//errs() << "ANALYZE\n";
	GI.analyze(getAnalysis<DominatorTreeWrapperPass>().getDomTree());
	return false;
}

void GenCondBlockSetLoopInfoWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
	//errs() << "LOOP DEP\n";
	AU.addRequired<DominatorTreeWrapperPass>();
	AU.setPreservesCFG();
	AU.setPreservesAll();
}

bool GenCondBlockSetLoopInfoPass::runOnFunction(Function &) {
	//errs() << "ANALYZE\n";
	GI.analyze(getAnalysis<DominatorTreeWrapperPass>().getDomTree());
	return false;
}

void GenCondBlockSetLoopInfoPass::getAnalysisUsage(AnalysisUsage &AU) const {
	//errs() << "LOOP DEP\n";
	AU.addRequired<DominatorTreeWrapperPass>();
	AU.setPreservesCFG();
	AU.setPreservesAll();
}
