//=============== Header file for getting a if-blocks forest ================//
//
//=====------------------------------------------------------------------=====//
//
// The following classes accounts for "natural" if-else or if-then blocks
// and rare gotos. Loops are treated completely differently and if-headers that
// are loop headers are not taken into account here.
//
//=====------------------------------------------------------------------=====//

#ifndef CONDBLOCKINFO_H_
#define CONDBLOCKINFO_H_

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


namespace llvm {

class CondBlockSet;
template <class BlockT, class CondBlockSetT> class CondTreeInfoBase;

// This is the cond block set base class
template <class BlockT, class CondBlockSetT>
class CondBlockSetBase {
// Parent condition block
	CondBlockSetT *ParentCondBlockSet;

// Header for the if-blocks
	BlockT *Header;

// Tail for the if-blocks. Note that Tail can be nullptr
	BlockT *Tail;

// Vector to store pointers to blocks in the if-blocks. These do not
// include the header and the tail.
	std::vector<BlockT *> CondBlocks;

// Vector to the subBlocks
	std::vector<CondBlockSetT *> SubCondBlockSets;

	const CondBlockSetBase<BlockT, CondBlockSetT> &
	operator=(const CondBlockSetBase<BlockT, CondBlockSetT> &) = delete;

	CondBlockSetBase(const CondBlockSetBase<BlockT, CondBlockSetT> &) = delete;

	friend class CondTreeInfoBase<BlockT, CondBlockSetT>;
	friend class CondBlockSet;
	/*
	~CondBlockSetBase() {
		for(auto *subCondBlockSets : SubCondBlockSets)
			subCondBlockSets->~CondBlockSetT();

		ParentCondBlockSet = nullptr;
		Header = nullptr;
		Tail = nullptr;
		CondBlocks.clear();
		SubCondBlockSets.clear();
	}
		*/
public:
	CondBlockSetBase(): ParentCondBlockSet(nullptr),
							 Header(nullptr), Tail(nullptr) {};

	std::vector<BlockT *> getCondBlocks() const {
		return CondBlocks;
	}

	std::vector<CondBlockSetT *> getSubCondBlockSets() const {
		return SubCondBlockSets;
	}

	const BlockT *getHeader() const {
		return Header;
	}

	const BlockT *getTail() const {
		return Tail;
	}

	CondBlockSetT *getParentCondBlockSet() const {
		return ParentCondBlockSet;
	}

	bool isCondBlockHeader(const BlockT *condBlock) const {
		return condBlock == Header;
	}

	bool isCondBlockTail(const BlockT *condBlock) const {
		return condBlock == Tail;
	}

	uint64_t getNumCondBlocks() const {
		return CondBlocks.size();
	}

	uint64_t getNumSubCondBlockSets() const {
		return SubCondBlockSets.size();
	}

	void setParentCondBlockSet(const CondBlockSetT *parent) {
		ParentCondBlockSet = const_cast<CondBlockSetT *>(parent);
	}

	uint64_t getCondBlockSetDepth() const {
		uint64_t depth = 1;
		CondBlockSetT *condBlockSet = ParentCondBlockSet;
		while(condBlockSet) {
			condBlockSet = condBlockSet->getParentCondBlockSet();
			depth++;
		}
		return depth;
	}

// Sets the header and puts it in the condBlock set
	void setHeader(BlockT *header) {
		Header = header;
	}

// Sets the tail and puts it in the condBlock set
	void setTail(BlockT *tailBlock) {
		Tail = tailBlock;
	}

	void addCondBlock(BlockT *block) {
		CondBlocks.push_back(block);
	}

	bool contains(const CondBlockSetT *blockset) const {
	// A condblock set contains itself
		if(blockset == this)
			return true;

		CondBlockSetT *condBlockSet = blockset->getParentCondBlockSet();
		while(!condBlockSet) {
			if(condBlockSet == this)
				return true;
			condBlockSet = condBlockSet->getParentCondBlockSet();
		}
		return false;
	}

	bool contains(const BlockT *block) const {
		if(find(CondBlocks.begin(), CondBlocks.end(), block) == CondBlocks.end())
			return false;
		return true;
	}

	bool isContainedIn(const CondBlockSetT *blockset) const {
	// A condblock set contains itself
		if(blockset == this)
			return true;

		CondBlockSetT *condBlockSet = getParentCondBlockSet();
		while(!condBlockSet) {
			if(condBlockSet == this)
				return true;
			condBlockSet = condBlockSet->getParentCondBlockSet();
		}
		return false;
	}

// Gets the condition for the condblock set
	Value *getCondition() const {
		return Header->getTerminator()->getOperand(0);
	}

	bool executesWhenConditionIsTrue() const {
		return contains(dyn_cast<BlockT>(Header->getTerminator()->getSuccessor(0)));
	}

	bool strictlyContainsCondBlockSet(const CondBlockSetT *) const;

	void addSubCondBlockSet(CondBlockSetT *blockset) {
		SubCondBlockSets.push_back(blockset);
	}

	void addChildCondBlockSet(CondBlockSetT *condBlockSet) {
		assert(condBlockSet && "Error: A null condBlock set cannot be added.");
		condBlockSet->ParentCondBlockSet = static_cast<CondBlockSetT *>(this);
		SubCondBlockSets.push_back(condBlockSet);
	}

// Function for pre-ordering the condBlocksets
	void preorderSubCondBlockSets(const DominatorTreeBase<BlockT, false> &domTree);

// Function for post-ordering the condBlocksets
	void postorderSubCondBlockSets(const DominatorTreeBase<BlockT, false> &domTree) {
	// Make sure that the top-level condBlocks are pre-ordered first
		preorderSubCondBlockSets(domTree);

	// Reverse the order of the std::vector now
		std::vector<CondBlockSetT *> postOrderCondBlockSets;
		typename std::vector<CondBlockSetT *>::reverse_iterator vect_it = SubCondBlockSets.rbegin();
		while(vect_it != SubCondBlockSets.rend()) {
			postOrderCondBlockSets.push_back(*vect_it);
			vect_it++;
		}
		SubCondBlockSets = postOrderCondBlockSets;
	}

// Use this API when the it does not matter if the condblocks are pre-ordered or not.
	void addBlock(const BlockT *);

// This is used to add a new sub-condblock set to this condblock set. This addition
// presumes that there was no major change made to the control flow graph such
// that the header, tail or any other block of this condblock set is majorly
// affected. This API assumes that the header and the tail of the new
// sub-condblock set are already set or will be explicitly set after.
	void addSubCondBlockSetToCondBlockSet(CondBlockSetT *);

// Sub-condblock set iterators
	using iterator = typename std::vector<CondBlockSetT *>::const_iterator;
	using reverse_iterator =
					typename std::vector<CondBlockSetT *>::const_reverse_iterator;

	iterator begin() const {
		return SubCondBlockSets.begin();
	}

	iterator end() const {
		return SubCondBlockSets.end();
	}

	reverse_iterator rbegin() const {
		return SubCondBlockSets.rbegin();
	}

	reverse_iterator rend() const {
		return SubCondBlockSets.rend();
	}

	bool empty() const {
		return SubCondBlockSets.empty();
	}

// Condblock iterators
	using block_iterator = typename std::vector<BlockT *>::const_iterator;

	block_iterator block_begin() const {
		return CondBlocks.begin();
	}

	block_iterator block_end() const {
		return CondBlocks.end();
	}

// API for printing the labels of basic blocks in the condblock set. There is no
// guarantee that the labels of the basic blocks will be printed properly. So this
// function is unsafe to use.
	void printCondBlockSet() {
	  // Print header of the condblock set even though it is not a part of condblock
	  // set per se.
		errs() << "******************* PRINTING CONDBLOCKS *********************\n";
		if(!Header) {
		  errs() << "NO HEADER EXISTS\n";
		} else {
		  errs() << "HEADER: ";
		  Header->printAsOperand(errs(), false);
		  errs() << "\n";
		}

	  // Print condblocks
		if(CondBlocks.empty()) {
			errs() << "NO CONDBLOCKS EXIST IN CONDBLOCK SET\n";
		} else {
		  errs() << "CONDBLOCKS: ";
		  typename std::vector<BlockT *>::iterator it = CondBlocks.begin();
		  while(it != CondBlocks.end()) {
			  (*it)->printAsOperand(errs(), false);
			  errs() << " ";
			  it++;
		  }
		  errs() << "\n";
		}

	  // Print tail of the condblock set
		if(!Tail) {
		  errs() << "NO TAIL EXISTS\n";
		} else {
		  errs() << "TAIL: ";
		  Tail->printAsOperand(errs(), false);
		  errs() << "\n";
		}
		errs() << "***************************************************************\n";
	}

// Print the blocks in the subsets of this condblock set
	void printSubCondBlockSets() {
		if(SubCondBlockSets.empty()) {
			errs() << "NO SUB-CONDBLOCK SET EXISTS!\n";
			return;
		}
		errs() << "===================== PRINTING CONDBLOCK SUBSET ===============\n";
		typename std::vector<CondBlockSetT *>::iterator it = SubCondBlockSets.begin();
		while(it != SubCondBlockSets.end()) {
			(*it)->printCondBlockSet();
			it++;
		}
		errs() << "==============================================================\n";
	}

	void printParentCondBlockSet() {
	// Print parent
		if(!ParentCondBlockSet) {
			errs() << "NO PARENT CONDBLOCK SET EXISTS!\n";
			return;
		}
		errs() << "================= PRINTING PARENT CONDBLOCK SET ==============\n";
		ParentCondBlockSet->printCondBlockSet();
		errs() << "=============================================================\n";
	}

	virtual void printCondBlockSetInfo() {
		errs() << "*************** PRINTING CONDBLOCK SET INFO *****************\n";

	// Print the condblock set whose parent needs printing
		printCondBlockSet();

	// Print parent cond block set
		printParentCondBlockSet();

	// Print the subcondblock sets
		printSubCondBlockSets();
		errs() << "*************************************************************\n";
	}
};

class CondBlockSet : public CondBlockSetBase<BasicBlock, CondBlockSet> {
private:
	CondBlockSet() = default;
	//~CondBlockSet() = default;

	friend class CondTreeInfoBase<BasicBlock, CondBlockSet>;
};

// This is the basic class for holding all the cond block sets
template <class BlockT, class CondBlockSetT>
class CondTreeInfoBase {
// Finds the inner most condBlock containing the given block
	 DenseMap<const BlockT *, CondBlockSetT *> CondBlockSetBlockMap;

// 	Vector to store pointers to top level condBlockSets
	std::vector<CondBlockSetT *> TopLevelCondBlockSets;

// Since the condblock sets appear in pairs, we set a map up to map the pairs
	DenseMap<const CondBlockSetT *, CondBlockSetT *> CondBlockSetsPairMap;

// Map tails of condblock tails to the condblock sets heads
	DenseMap<const BlockT *, BlockT *> TopLevelTailsToHeadsMap;

	const CondTreeInfoBase<BlockT, CondBlockSetT> &
		operator=(CondTreeInfoBase<BlockT, CondBlockSetT> &) = delete;

	CondTreeInfoBase(CondTreeInfoBase<BlockT, CondBlockSetT> &) = delete;

public:
	CondTreeInfoBase() = default;

	/*
	~CondTreeInfoBase() {
		for(auto *condBlockSets : TopLevelCondBlockSets)
			condBlockSets->~CondBlockSetT();

	// Clear the tree info structures
		CondBlockSetBlockMap.shrink_and_clear();
		TopLevelCondBlockSets.clear();
		CondBlockSetsPairMap.shrink_and_clear();
	}
	*/

	CondBlockSetT *AllocateCondBlockSet() {
		return new CondBlockSetT();
	}

	std::vector<CondBlockSetT *> &getTopLevelCondBlockSets() const {
		return TopLevelCondBlockSets;
	}

	BlockT *getHeaderForTopLevelTail(const BlockT *tail) const {
		return TopLevelTailsToHeadsMap.lookup(tail);
	}

	bool isTopLevelCondBlockSet(CondBlockSetT *blockset) const {
		if(!blockset)
			return false;
		if(find(TopLevelCondBlockSets.begin(), TopLevelCondBlockSets.end(), blockset)
					== TopLevelCondBlockSets.end()) {
			return false;
		}
		return true;
	}

	void addTopLevelCondBlockSet(CondBlockSetT *blockset) {
	// Add top level condblock set
		TopLevelCondBlockSets.push_back(blockset);

	// Map tails to the head of the condblock set
		if(blockset->getTail()) {
			errs() << "TOP LEVEL TAIL: ";
			blockset->getTail()->printAsOperand(errs(), false);
			errs() << "\n";
			if(const BlockT *tail = blockset->getTail()) {
				TopLevelTailsToHeadsMap[tail] =
						const_cast<BlockT *>(blockset->getHeader());
				errs() << "TAIL MAPPED\n";
			}
		}
	}

	uint64_t getNumTopLevelCondBlockSets() const {
		return TopLevelCondBlockSets.size();
	}

	void addToMap(CondBlockSetT *blockset, const BlockT *block) {
	// Add the block and blockset pair in the map
		CondBlockSetBlockMap[block] = blockset;
	}

	void addToMap(BlockT *head, const BlockT *tail) {
	// Add the head to the tail map
		TopLevelTailsToHeadsMap[tail] = head;
	}

// Get the inner-most condblock set for a given basic block
	CondBlockSetT *getCondBlockSetFor(const BlockT *block) const {
		return CondBlockSetBlockMap.lookup(block);
	}

	void changeCondBlockSetFor(BlockT *block, CondBlockSetT *condBlockSet) {
		if(!condBlockSet)
			CondBlockSetBlockMap.erase(block);
		else
			CondBlockSetBlockMap[block] = condBlockSet;
	}

	CondBlockSetT *operator[](const BlockT *block) const {
		return CondBlockSetBlockMap.lookup(block);
	}

// Add a top-level condblockset. This is used when new top-level condblock sets
//are added explicitly. It is not to be used when an existing top-level block is
// modified in anyway.
	void addTopLevelCondBlockSet(CondBlockSetT *,
								const DominatorTreeBase<BlockT, false> &);

	void addCondBlockSetPair(const CondBlockSetT *condBlockSetKey,
							 CondBlockSetT *condBlockSet) {
		CondBlockSetsPairMap[condBlockSetKey] = condBlockSet;
	}

	void addCondBlockSetPair(const CondBlockSetT *condBlockSet1,
							 const CondBlockSetT *condBlockSet2) {
		CondBlockSetsPairMap[condBlockSet1] = const_cast<CondBlockSetT *>(condBlockSet2);
		CondBlockSetsPairMap[condBlockSet2] = const_cast<CondBlockSetT *>(condBlockSet1);
	}

	bool isCondBlockSetHeader(const BlockT *potentialHeader) const {
		return getCondBlockSetForHeader(potentialHeader) != nullptr;
	}

	CondBlockSetT *getCondBlockSetForHeader(const BlockT *potentialHeader) const;

	bool isCondBlockSetTail(const BlockT *) const;

// Function for pre-ordering the condBlocksets
	void preorderTopLevelCondBlockSets(const DominatorTreeBase<BlockT, false> &);

// Function to post-order the condBlocksets
	void postorderTopLevelCondBlockSets(const DominatorTreeBase<BlockT, false> &);

// Computes the CondTreeInfo forest
	void analyze(const DominatorTreeBase<BlockT, false> &);

// Iterator for the top-level cond blocksets
	using iterator = typename std::vector<CondBlockSetT *>::const_iterator;
	using reverse_iterator =
					typename std::vector<CondBlockSetT *>::const_reverse_iterator;

	iterator begin() {
		return TopLevelCondBlockSets.begin();
	}

	iterator end() {
		return TopLevelCondBlockSets.end();
	}

	reverse_iterator rbegin() {
		return TopLevelCondBlockSets.rbegin();
	}

	reverse_iterator rend() {
		return TopLevelCondBlockSets.rend();
	}

	void printTopLevelCondBlockSets() {
		iterator it = begin();
		if(it == end()) {
			errs() << "NO TOP LEVEL CONDBLOCK SETS EXIST\n";
			return;
		}
		errs() << "============== PRINTING TOP-LEVEL CONDBLOCK SETS ============\n";
		while(it != end()) {
			(*it)->printCondBlockSet();
			it++;
		}
		errs() << "=============================================================\n";
	}

	CondBlockSetT *getPartnerCondBlockSet(const CondBlockSetT *condBlockSet) const {
		return CondBlockSetsPairMap.lookup(condBlockSet);
	}

// Get a vector of condblock sets in order of dominance and reverse order.
// They include all the condblocksets in the forest.
	std::vector<CondBlockSetT *> getCondBlockSetsInPreorder();

	std::vector<CondBlockSetT *> getCondBlockSetsInPostorder() {
		std::vector<CondBlockSetT *> postorderCondBlockSetVect;
		std::vector<CondBlockSetT *> condBlockSetVect = getCondBlockSetsInPreorder();
		typename std::vector<CondBlockSetT *>::const_reverse_iterator it = condBlockSetVect.rbegin();
		while(it != condBlockSetVect.rend()) {
			postorderCondBlockSetVect.push_back((*it));
			it++;
		}
		return postorderCondBlockSetVect;
	}

// Print a vector of condblocksets
	void printCondBlockSetVector(
							const std::vector<CondBlockSetT *> &condBlockSetsVect) {
		errs() << "=========== PRINTING CONDBLOCK SETS VECTOR =================\n";
		typename std::vector<CondBlockSetT *>::const_iterator it = condBlockSetsVect.begin();
		while(it != condBlockSetsVect.end()) {
			(*it)->printCondBlockSetInfo();
			it++;
		}
		errs() << "==============================================================\n";
	}
};

class CondTreeInfo : public CondTreeInfoBase<BasicBlock, CondBlockSet> {
public:
	CondTreeInfo() = default;
	//~CondTreeInfo() = default;
};

}  // namespace llvm

#endif // CONDBLOCKINFO_H_
