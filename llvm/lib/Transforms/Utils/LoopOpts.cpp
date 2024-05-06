#include "llvm/Transforms/Utils/LoopOpts.h"

using namespace llvm;

bool is_loopInvariant(Instruction *inst)
{
    if (!inst->isBinaryOp())
        return false;
    Value *val1 = inst->getOperand(0);
    Value *val2 = inst->getOperand(1);
}

PreservedAnalyses LoopOpts::run (Loop &L, LoopAnalysisManager &LAM, 
                                    LoopStandardAnalysisResults &LAR, LPMUpdater &LU)
{
    outs() << L.getLoopPreheader() << "\n";
    BasicBlock *preheader = L.getLoopPreheader();
    outs() << L.getHeader() << "\n";
    // outs() << L.getBlocks() << "\n";

    for (Loop::block_iterator BI = L.block_begin(); BI != L.block_end(); ++BI)
    {
        outs() << BI << "\n";
        BasicBlock const *BB = dyn_cast<BasicBlock const>(BI);
        for (BasicBlock::const_iterator i = BB->begin(); i != BB->end(); i++)
        {
            const Instruction *inst = dyn_cast<Instruction>(BB);

        }
    }
    return PreservedAnalyses::all();
}