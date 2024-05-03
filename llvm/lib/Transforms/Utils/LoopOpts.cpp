#include "llvm/Transforms/Utils/LoopOpts.h"

using namespace llvm;

PreservedAnalyses LoopOpts::run (Loop &L, LoopAnalysisManager &LAM, 
                                    LoopStandardAnalysisResults &LAR, LPMUpdater &LU)
{
    outs() << L.getLoopPreheader() << "\n";
    outs() << L.getHeader() << "\n";
    // outs() << L.getBlocks() << "\n";
    for (Loop::block_iterator BI = L.block_begin(); BI != L.block_end(); ++BI)
    {
        outs() << BI << "\n";
    }
    return PreservedAnalyses::all();
}