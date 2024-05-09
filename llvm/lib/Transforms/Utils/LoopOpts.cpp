#include "llvm/Transforms/Utils/LoopOpts.h"

using namespace llvm;

bool isAlreadyLoopInvariant(Instruction *inst)
{
    return inst->getMetadata("invariant");
}

bool isValueInvariant(Value *v, Loop* L)
{
    Instruction *v_inst = dyn_cast<Instruction>(v);
    if (!v_inst || isAlreadyLoopInvariant(v_inst) || !L->contains(v_inst))
        return true;
    
    Constant *c_inst = dyn_cast<Constant>(v);
    if (c_inst)
        return true;
    
    return false;
}

bool isLoopInvariant(const Instruction *inst, Loop* L)
{
    if (!inst->isBinaryOp())
        return false;
    Value *val1 = inst->getOperand(0);
    Value *val2 = inst->getOperand(1);
    
    return isValueInvariant(val1, L) && isValueInvariant(val2, L);
}

PreservedAnalyses LoopOpts::run (Loop &L, LoopAnalysisManager &LAM, 
                                    LoopStandardAnalysisResults &LAR, LPMUpdater &LU)
{
    outs() << L.getLoopPreheader() << "\n";
    BasicBlock *preheader = L.getLoopPreheader();
    outs() << L.getHeader() << "\n";
    // outs() << L.getBlocks() << "\n";

    Loop *Loop = &L;
    for (Loop::block_iterator BI = L.block_begin(); BI != L.block_end(); ++BI)
    {
        outs() << BI << "\n";
        BasicBlock const *BB = dyn_cast<BasicBlock const>(BI);
        for (BasicBlock::const_iterator i = BB->begin(); i != BB->end(); i++)
        {
            // const_cast translate a const object into a non constant one
            // in this case const Instruction into Instruction.
            Instruction *inst = const_cast<Instruction *>(&(*i));
            if (isLoopInvariant(inst, Loop))
            {
                LLVMContext &C = inst->getContext();
                MDNode *N = MDNode::get(C, MDString::get(C, ""));
                inst->setMetadata("invariant", N);
            }
        }
    }
    return PreservedAnalyses::all();
}