#include "llvm/Transforms/Utils/LoopFusion.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
//#include <llvm/Analysis/LoopInfo.h>

using namespace llvm;

bool isAdjacent (Loop *l1, Loop *l2)
{
    // check for all the exiting blocks of l1
    SmallVector<BasicBlock*, 4> exit_blocks;
    l1->getUniqueNonLatchExitBlocks(exit_blocks);
    for (BasicBlock *BB : exit_blocks)
    {
        if (BB != (l2->isGuarded() ? dyn_cast<BasicBlock>(l2->getLoopGuardBranch()) : l2->getLoopPreheader()))
            return false;
    }
    return true;
}



PreservedAnalyses LoopFusion::run (Function &F,FunctionAnalysisManager &AM)
{
    LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
    DominatorTree &DT = AM.getResult<LoopStandardAnalysisResults>().getDomTree();
    for (Loop *L : LI)
    {
        outs() << *L << "\n"; 
    }

    return PreservedAnalyses::all();
}