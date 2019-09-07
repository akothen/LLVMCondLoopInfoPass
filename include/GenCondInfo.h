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

#ifndef GENCONDINFO_H_
#define GENCONDINFO_H_

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
#include "llvm/PassSupport.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopInfoImpl.h"
#include "CondBlockBase.h"
#include "CondBlockBaseImpl.h"

namespace llvm {

template<class BlockT, class LoopT, class CondBlockSetT> class GenLoopBase;
template<class BlockT, class LoopT, class CondBlockSetT> class GenCondBlockSetLoopInfoBase;
class GenLoop;
class GenCondBlockSet;

// This class holds info about loops and condblock sets nests
template<class BlockT, class LoopT, class CondBlockSetT>
class GenCondBlockSetBase: public CondBlockSetBase<BlockT, CondBlockSetT> {
// Parent Loop
	LoopT *ParentLoop;

// Sub-loops
	std::vector<LoopT *> SubLoops;

	const GenCondBlockSetBase<BlockT, LoopT, CondBlockSetT> &
	operator=(const GenCondBlockSetBase<BlockT, LoopT, CondBlockSetT> &) = delete;

	GenCondBlockSetBase(
			const GenCondBlockSetBase<BlockT, LoopT, CondBlockSetT> &) = delete;

	friend class GenCondBlockSetLoopInfoBase<BlockT, LoopT, CondBlockSetT> ;

	/*
	 ~GenCondBlockSetBase() {
	 for(auto *subLoops : SubLoops)
	 subLoops->~GenCondBlockSetBase();

	 ParentLoop = nullptr;
	 SubLoops.clear();
	 }
	 */
public:
	GenCondBlockSetBase() : ParentLoop(nullptr) {}

	const LoopT *getParentLoop() const {
		return ParentLoop;
	}

	std::vector<LoopT *> &getSubLoops() const {
		return SubLoops;
	}

	void setParentLoop(const LoopT *parent) {
		ParentLoop = const_cast<LoopT *>(parent);
	}

	bool isParentLoop(const LoopT *loop) const {
		return loop == ParentLoop;
	}

	void addSubLoop(LoopT *loop) {
		SubLoops.push_back(loop);
	}

	bool containsSubLoop(const LoopT *loop) const {
		if(find(SubLoops.begin(), SubLoops.end(), loop) == SubLoops.end())
			return false;
		return true;
	}

	bool contains(const LoopT *loop) const {
		if(const CondBlockSetT *condBlockSet = loop->getParentCondBlockSet())
			return contains(condBlockSet);
		return false;
	}

	using CondBlockSetBase<BlockT, CondBlockSetT>::contains;

	uint64_t getLoopDepth() const {
		uint64_t depth = 1;
		LoopT *loop = ParentLoop;
		while (loop) {
			loop = loop->getParentLoop();
			depth++;
		}
		return depth;
	}

	bool isContainedIn(const LoopT *parentLoop) const {
		LoopT * loop = ParentLoop;
		while(!loop) {
			if (loop == parentLoop)
				return true;
			loop = loop->getParentLoop();
		}
		return false;
	}

// Function for pre-ordering the subloops
	void preorderSubLoops(const DominatorTreeBase<BlockT, false> &domTree);

// Function for post-ordering the subloops
	void postorderSubLoops(const DominatorTreeBase<BlockT, false> &);

// Subloops iterator functions
	using loop_iterator = typename std::vector<LoopT *>::const_iterator;
	using reverse_loop_iterator =
								typename std::vector<LoopT *>::const_reverse_iterator;

	loop_iterator loop_begin() const {
		return SubLoops.begin();
	}

	loop_iterator loop_end() const {
		return SubLoops.end();
	}

	reverse_loop_iterator loop_rbegin() const {
		return SubLoops.rbegin();
	}

	reverse_loop_iterator loop_rend() const {
		return SubLoops.rend();
	}

	void printParentLoop() {
		errs() << "******************* PRINTING PARENT LOOP ***********************\n";
		if (ParentLoop)
			ParentLoop->printLoop();
		else
			errs() << "NO PARENT LOOP\n";
		errs() << "****************************************************************\n";
	}

	void printSubLoops() {
		errs() << "*********************** PRINTING SUBLOOPS **********************\n";
		if (SubLoops.empty()) {
			errs() << "NO SUBLOOPS EXIST\n";
		} else {
			typename std::vector<LoopT *>::iterator subloop_it =
					SubLoops.begin();
			while (subloop_it != SubLoops.end()) {
				(*subloop_it)->printLoop();
				subloop_it++;
			}
		}
		errs() << "****************************************************************\n";
	}

	virtual void printCondBlockSetInfo() {
		errs() << "*************** PRINTING CONDBLOCK SET INFO ********************\n";

		// Print the condblock set whose parent needs printing
		this->printCondBlockSet();

		// Print parent cond block set
		this->printParentCondBlockSet();

		// Print the subcondblock sets
		this->printSubCondBlockSets();

		// Print of parent loop
		printParentLoop();

		// Print subloops
		printSubLoops();
		errs() << "****************************************************************\n";
	}
};

class GenCondBlockSet :
				public GenCondBlockSetBase<BasicBlock, GenLoop, GenCondBlockSet> {
private:
	GenCondBlockSet() = default;
	//~GenCondBlockSet()  = default;

	friend class GenCondBlockSetLoopInfoBase<BasicBlock, GenLoop, GenCondBlockSet>;
	friend class CondTreeInfoBase<BasicBlock, GenCondBlockSet>;
};

template<class BlockT, class LoopT, class CondBlockSetT>
class GenLoopBase: public LoopBase<BlockT, LoopT> {
// Parent CondBlock set
	CondBlockSetT *ParentCondBlockSet;

// Sub-cond block set
	std::vector<CondBlockSetT *> SubCondBlockSets;

	const GenLoopBase<BlockT, LoopT, CondBlockSetT> &
	operator=(const GenLoopBase<BlockT, LoopT, CondBlockSetT> &) = delete;

	GenLoopBase(const GenLoopBase<BlockT, LoopT, CondBlockSetT> &) = delete;

	friend class GenCondBlockSetLoopInfoBase<BlockT, LoopT, CondBlockSetT> ;

	/*
	 ~GenLoopBase() {
	 for(auto *subCondBlockSet : SubCondBlockSets)
	 subCondBlockSet->~GenLoopBase();

	 SubCondBlockSets.clear();
	 ParentCondBlockSet = nullptr;
	 }
	 */
public:
	GenLoopBase() :
			ParentCondBlockSet(nullptr) {
	}

	explicit GenLoopBase(BlockT *block) :
			ParentCondBlockSet(nullptr), LoopBase<BlockT, LoopT>(block) {
	}

	void setParentCondBlockSet(const CondBlockSetT *condBlockSet) {
		ParentCondBlockSet = const_cast<CondBlockSetT *>(condBlockSet);
	}

	const CondBlockSetT *getParentCondBlockSet() const {
		return ParentCondBlockSet;
	}

	std::vector<CondBlockSetT *> getSubCondBlockSets() const {
		return SubCondBlockSets;
	}

	uint64_t getNumSubCondSets() const {
		return SubCondBlockSets.size();
	}

	void addSubCondBlockSet(const CondBlockSetT *condBlockSet) {
		SubCondBlockSets.push_back(const_cast<CondBlockSetT *>(condBlockSet));
	}

	bool containsSubCondBlockSet(const CondBlockSetT *condBlockSet) {
		if (find(SubCondBlockSets.begin(), SubCondBlockSets.end(),
				const_cast<CondBlockSetT *>(condBlockSet))
				== SubCondBlockSets.end()) {
			return false;
		}
		return true;
	}

	bool contains(const CondBlockSetT *condBlockSet) const {
		if(const LoopT *loop = condBlockSet->getParentLoop())
			return contains(loop);
		return false;
	}

	using LoopBase<BlockT, LoopT>::contains;

// Iterators for sub-condblock sets and sub-condloops
	using condblockset_iterator =
							typename std::vector<CondBlockSetT *>::const_iterator;
	using reverse_condblockset_iterator =
	typename std::vector<CondBlockSetT *>::const_reverse_iterator;

	condblockset_iterator condblockset_begin() const {
		return SubCondBlockSets.begin();
	}

	condblockset_iterator condblockset_end() const {
		return SubCondBlockSets.end();
	}

	reverse_condblockset_iterator condblockset_rbegin() const {
		return SubCondBlockSets.rbegin();
	}

	reverse_condblockset_iterator condblockset_rend() const {
		return SubCondBlockSets.rend();
	}

// Preorder the subcondblock sets in all the loops
	void preorderSubCondBlockSets(const DominatorTreeBase<BlockT, false> &);

// Function for post-ordering the condBlocksets
	void postorderSubCondBlockSets(const DominatorTreeBase<BlockT, false> &);

	/*
	 bool contains(const CondBlockSetT *condBlockSet) const {
	 const LoopT *loop = condBlockSet->getParentLoop();
	 while(!loop) {
	 if(loop == this)
	 return true;
	 loop = loop->getParentLoop();
	 }
	 return false;
	 }
	 */
	bool isContainedIn(const LoopT *parentLoop) const {
		if (parentLoop == this)
			return true;

		LoopT * loop = this->getParentLoop();
		while (!loop) {
			if (loop == parentLoop)
				return true;
			loop = loop->getParentLoop();
		}
		return false;
	}

	bool isContainedIn(const CondBlockSetT *blockSet) const {
		CondBlockSetT *condBlockSet = getParentCondBlockSet();
		while (!condBlockSet) {
			if (condBlockSet == this)
				return true;
			condBlockSet = condBlockSet->getParentCondBlockSet();
		}
		return false;
	}

// Print all the information about loops
	void printLoop() {
		errs() << "======================= PRINTING LOOP ==========================\n";
		errs() << "LOOP HEADER: ";
		BlockT *header = this->getHeader();
		header->printAsOperand(errs(), false);
		errs() << "\nLOOP BLOCKS: ";
		std::vector<BlockT *> loopBlocks = this->getBlocksVector();
		typename std::vector<BlockT *>::const_iterator it = loopBlocks.begin();
		while (it != loopBlocks.end()) {
			if (*it != header)
				(*it)->printAsOperand(errs(), false);
			errs() << " ";
			it++;
		}
		errs() << "\n==============================================================\n";
	}

	void printParentCondBlockSet() {
		if (!ParentCondBlockSet) {
			errs() << "NO PARENT CONDBLOCK SET EXISTS\n";
			return;
		}
		errs() << "**************** PRINTING PARENT CONDBLOCK SET *****************\n";
		ParentCondBlockSet->printCondBlockSet();
		errs() << "****************************************************************\n";
	}

	void printSubCondBlockSets() {
		if (SubCondBlockSets.empty()) {
			errs() << "NO SUBCONDBLOCK SETS EXIST\n";
			return;
		}
		errs() << "******************* PRINTING SUBCONDBLOCK SETS *****************\n";
		typename std::vector<CondBlockSetT *>::iterator it =
				SubCondBlockSets.begin();
		while (it != SubCondBlockSets.end()) {
			(*it)->printCondBlockSet();
			it++;
		}
		errs() << "****************************************************************\n";
	}

	void printParentLoop() {
		errs() << "---------------------- PRINT PARENT LOOP -----------------------\n";
		this->getParentLoop()->printLoop();
		errs() << "----------------------------------------------------------------\n";
	}

	void printSubLoops() {
		errs() << "+++++++++++++++++++++ PRINT SUBLOOPS +++++++++++++++++++++++++++\n";
		typename LoopBase<BlockT, LoopT>::iterator it = this->begin();
		while (it != this->end()) {
			(*it)->printLoop();
			it++;
		}
		errs() << "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
	}

	virtual void printLoopInfo() {
		errs() << "===================== PRINTING CONDLOOP INFO ===================\n";

		// Print this loop
		printLoop();

		// Print parent loop
		printParentLoop();

		// Print subloops
		printSubLoops();

		// Print parent cond block sets
		printParentCondBlockSet();

		// Print sub-condblock sets
		printSubCondBlockSets();
		errs() << "================================================================\n";
	}
};

class GenLoop: public GenLoopBase<BasicBlock, GenLoop, GenCondBlockSet> {
private:
	GenLoop() = default;
	//~GenLoop() = default;
	explicit GenLoop(BasicBlock *block)
			: GenLoopBase<BasicBlock, GenLoop, GenCondBlockSet>(block) {}

	friend class GenCondBlockSetLoopInfoBase<BasicBlock, GenLoop, GenCondBlockSet>;
	friend class LoopInfoBase<BasicBlock, GenLoop>;
};

template<class BlockT, class LoopT, class CondBlockSetT>
class GenCondBlockSetLoopInfoBase: private LoopInfoBase<BlockT, LoopT>,
								   private CondTreeInfoBase<BlockT, CondBlockSetT> {
public:
// Loop and Condblock set iterators and functions
	using loop_iterator = typename LoopInfoBase<BlockT, LoopT>::iterator;
	using reverse_loop_iterator =
								typename LoopInfoBase<BlockT, LoopT>::reverse_iterator;

	loop_iterator loop_begin() const {
		return LoopInfoBase<BlockT, LoopT>::begin();
	}

	loop_iterator loop_end() const {
		LoopInfoBase<BlockT, LoopT>::end();
	}

	reverse_loop_iterator reverse_loop_begin() const {
		return LoopInfoBase<BlockT, LoopT>::rbegin();
	}

	reverse_loop_iterator reverse_loop_end() const {
		return LoopInfoBase<BlockT, LoopT>::rend();
	}

	using condblockset_iterator =
								typename CondTreeInfoBase<BlockT, CondBlockSetT>::iterator;
	using reverse_condblockset_iterator =
					typename CondTreeInfoBase<BlockT, CondBlockSetT>::reverse_iterator;

	condblockset_iterator condblockset_begin() const {
		return CondTreeInfoBase<BlockT, CondBlockSetT>::begin();
	}

	condblockset_iterator condblockset_end() const {
		return CondTreeInfoBase<BlockT, CondBlockSetT>::end();
	}

	reverse_condblockset_iterator reverse_condblockset_begin() const {
		return CondTreeInfoBase<BlockT, CondBlockSetT>::rbegin();
	}

	reverse_condblockset_iterator reverse_condblockset_end() const {
		return CondTreeInfoBase<BlockT, CondBlockSetT>::rend();
	}

	void analyze(const DominatorTreeBase<BlockT, false> &domTree) {
		// Create loop and condblock set forests separately
		//LoopInfoBase<BlockT, LoopT>::analyze(domTree);

		errs() << "----------- ANALYZING LOOP INFO -------------\n";
		LoopInfoBase<BlockT, LoopT>::analyze(domTree);
		//this->analyzeCondBlockSets(domTree);

		errs() << "----------- ANALYZING COND BLOCK SET INFO --------\n";
		CondTreeInfoBase<BlockT, CondBlockSetT>::analyze(domTree);

		errs() << "--------------BIND CONDBLOCKSET INFO TO LOOP INFO----------\n";
		bindCondBlockSetTreeToLoopTree(domTree);
		errs() << "--------------BIND LOOP INFO TO CONDBLOCKSET INFO ---------\n";
		bindLoopTreeToCondBlockSetTree(domTree);
	}

	void bindCondBlockSetTreeToLoopTree(const DominatorTreeBase<BlockT, false> &);

	void bindLoopTreeToCondBlockSetTree(const DominatorTreeBase<BlockT, false> &);

	/*
	 // Create and add a new condblock set to the condloop
	 void addSubCondBlockSetToCondLoop(const LoopT *condLoop,
	 const CondBlockSetT *condBlockSet) {
	 assert(condLoop && "Error: Cannot add a condblock set to a null condloop\n");
	 assert(condBlockSet && "Error: Cannot add a null condblock set to a condloop\n");

	 // Add this condblock set to the condloops and the parent condloops
	 LoopT *checkCondLoop = const_cast<LoopT *>(condLoop);
	 while(checkCondLoop) {
	 checkCondLoop->addSubCondBlockSet(condBlockSet);

	 // We cannot be sure about the order of the sub-condblock sets in the
	 // sub-condblock sets list. So we assume that the list is not pre-ordered.
	 checkCondLoop->setSubCondBlockSetsPreordered(false);
	 checkCondLoop = checkCondLoop->getParentLoop();
	 }

	 // Map all the condblocks of this condblock set to the condloop tree
	 CondBlockSetT::condBlock_iterator it =
	 const_cast<CondBlockSetT *>(condBlockSet)->condBlock_begin();
	 while(it != const_cast<CondBlockSetT *>(condBlockSet)->condBlock_end()) {
	 changeLoopFor(*it, const_cast<LoopT *>(condLoop));
	 it++;
	 }
	 }
	 */

// CondBlock set tree info
	/*
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::addTopLevelCondBlockSetToVect;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::addToMap;
	 */

	bool isAnExitingLoopBlock(const BlockT *block) const {
		assert(block && "Error: An exiting loop block cannot be null.");
		LoopT *loop = LoopInfoBase<BlockT, LoopT>::getLoopFor(block);
		return loop->isLoopExiting(block);
	}

// Functions from Loop tree
	using LoopInfoBase<BlockT, LoopT>::getLoopFor;
	using LoopInfoBase<BlockT, LoopT>::addTopLevelLoop;
	using LoopInfoBase<BlockT, LoopT>::getLoopsInPreorder;
	using LoopInfoBase<BlockT, LoopT>::getLoopDepth;
	using LoopInfoBase<BlockT, LoopT>::isLoopHeader;
	using LoopInfoBase<BlockT, LoopT>::removeLoop;
	using LoopInfoBase<BlockT, LoopT>::changeLoopFor;
	using LoopInfoBase<BlockT, LoopT>::changeTopLevelLoop;
	using LoopInfoBase<BlockT, LoopT>::removeBlock;
	using LoopInfoBase<BlockT, LoopT>::isNotAlreadyContainedIn;
	using LoopInfoBase<BlockT, LoopT>::AllocateLoop;

	std::vector<LoopT *> getLoopsInPostorder() {
	// Get the loops in preorder and reverse order the loops
		SmallVector<LoopT *, 4> preorderedLoopsVect =
				LoopInfoBase<BlockT, LoopT>::getLoopsInPreorder();
		std::vector<LoopT *> postorderedLoopsVect;
		while(!preorderedLoopsVect.empty()) {
			postorderedLoopsVect.push_back(preorderedLoopsVect.back());
			preorderedLoopsVect.pop_back();
		}
		return postorderedLoopsVect;
	}

// Functions from condblockset tree
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::isTopLevelCondBlockSet;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::getCondBlockSetFor;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::getNumTopLevelCondBlockSets;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::postorderTopLevelCondBlockSets;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::preorderTopLevelCondBlockSets;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::getCondBlockSetsInPreorder;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::getCondBlockSetsInPostorder;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::isCondBlockSetHeader;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::addTopLevelCondBlockSet;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::addCondBlockSetPair;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::isCondBlockSetTail;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::getPartnerCondBlockSet;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::changeCondBlockSetFor;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::AllocateCondBlockSet;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::getCondBlockSetForHeader;
	 using CondTreeInfoBase<BlockT, CondBlockSetT>::getHeaderForTopLevelTail;

// Printing functions
	void printCondBlockSetVector(
					const std::vector<CondBlockSetT *> &condBlockSetsVect) {
		CondTreeInfoBase<BlockT, CondBlockSetT>
											::printCondBlockSetVector(condBlockSetsVect);
	}

	void printTopLevelCondBlockSets() {
		CondTreeInfoBase<BlockT, CondBlockSetT>::printTopLevelCondBlockSets();
	}

	//using CondTreeInfoBase<BlockT, CondBlockSetT>::printCondBlockSetVector;
	//using CondTreeInfoBase<BlockT, CondBlockSetT>::printTopLevelCondBlockSets;

	void printTopLevelCondLoops() const {
		errs() << "*************** PRINTING TOP LEVEL CONDLOOPS *******************\n";
		typename LoopInfoBase<BlockT, LoopT>::iterator it = LoopInfoBase<BlockT,
				LoopT>::begin();
		while (it != LoopInfoBase<BlockT, LoopT>::end()) {
			(*it)->printLoopInfo();
			it++;
		}
		errs() << "****************************************************************\n";
	}
};

class GenCondBlockSetLoopInfo: public GenCondBlockSetLoopInfoBase<BasicBlock,
		GenLoop, GenCondBlockSet> {
public:
	GenCondBlockSetLoopInfo() = default;
	//~GenCondBlockSetLoopInfo() = default;
};



void initializeGenCondBlockSetLoopInfoWrapperPassPass(PassRegistry &);

// The legacy pass manager's analysis pass to compute loop information.
class GenCondBlockSetLoopInfoWrapperPass : public FunctionPass {
	GenCondBlockSetLoopInfo GI;

public:
	static char ID; // Pass identification, replacement for typeid

	GenCondBlockSetLoopInfoWrapperPass() : FunctionPass(ID) {
		//errs() << "INIT ANALYZE\n";
		initializeGenCondBlockSetLoopInfoWrapperPassPass(
							*PassRegistry::getPassRegistry());
	}

	GenCondBlockSetLoopInfo &getGenCondInfoWrapperPassInfo() {
		return GI;
	}
	const GenCondBlockSetLoopInfo &getGenCondInfoWrapperPassInfo() const {
		return GI;
	}

// Calculate the natural loop information for a given function.
	bool runOnFunction(Function &F) override;

	void getAnalysisUsage(AnalysisUsage &AU) const override;

	bool doInitialization(Module &M) const {
		//errs() << "HERE\n";
		return false;
	}

	bool doFinalization(Module &M) const {
		return false;
	}
};

void initializeGenCondBlockSetLoopInfoPassPass(PassRegistry &);

// The legacy pass manager's analysis pass to compute loop information.
class GenCondBlockSetLoopInfoPass : public FunctionPass {
	GenCondBlockSetLoopInfo GI;

public:
	static char ID; // Pass identification, replacement for typeid

	GenCondBlockSetLoopInfoPass() : FunctionPass(ID) {
		//errs() << "INIT ANALYZE\n";
		//initializeGenCondBlockSetLoopInfoWrapperPassPass(
			//				*PassRegistry::getPassRegistry());
	}

// Calculate the natural loop information for a given function.
	bool runOnFunction(Function &F) override;

	void getAnalysisUsage(AnalysisUsage &AU) const override;

	bool doInitialization(Module &M) const {
		//errs() << "HERE\n";
		return false;
	}

	bool doFinalization(Module &M) const {
		return false;
	}
};

}  // namespace llvm

#endif  // GENCONDINFO_H_
