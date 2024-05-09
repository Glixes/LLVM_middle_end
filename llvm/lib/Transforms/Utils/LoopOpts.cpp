#include "llvm/Transforms/Utils/LoopOpts.h"

using namespace llvm;

bool isAlreadyLoopInvariant(Instruction *inst, std::unordered_map<const Instruction*, bool> invariant_map)
{
    outs() << "Analyzing map: " << invariant_map[inst] << "\n";
    return invariant_map[inst];
    // return inst->getMetadata("invariant");
}

bool isValueInvariant(Value *v, Loop* L, std::unordered_map<const Instruction*, bool> invariant_map)
{
    Instruction *v_inst = dyn_cast<Instruction>(v);
    outs() << "Is value " << v_inst << " invariant?\n";
    if (!v_inst || isAlreadyLoopInvariant(v_inst, invariant_map) || !L->contains(v_inst))
        return true;
    
    Constant *c_inst = dyn_cast<Constant>(v);
    outs() << "Is the value " << c_inst << " constant?\n";
    if (c_inst)
        return true;
    
    return false;
}

bool isLoopInvariant(const Instruction *inst, Loop* L, std::unordered_map<const Instruction*, bool> invariant_map)
{
    if (!inst->isBinaryOp())
        return false;
    Value *val1 = inst->getOperand(0);
    Value *val2 = inst->getOperand(1);
    outs() << "Analyzing operands: " << *val1 << ", " << *val2 << "\n";
    
    return isValueInvariant(val1, L, invariant_map) && isValueInvariant(val2, L, invariant_map);
}

PreservedAnalyses LoopOpts::run (Loop &L, LoopAnalysisManager &LAM, 
                                    LoopStandardAnalysisResults &LAR, LPMUpdater &LU)
{
    std::unordered_map<const Instruction*, bool> invariant_map;
    
    outs() << "Pre-header: " << *(L.getLoopPreheader()) << "\n";
    outs() << "Header: " << *(L.getHeader()) << "\n";
    // outs() << L.getBlocks() << "\n";
    Loop *Loop = &L;
    for (Loop::block_iterator BI = L.block_begin(); BI != L.block_end(); ++BI)
    {
        BasicBlock const *BB = dyn_cast<BasicBlock const>(*BI);
        outs() << "Basic block: " << *BB << "\n";
        for (BasicBlock::const_iterator i = BB->begin(); i != BB->end(); i++)
        {
            // const_cast translate a const object into a non constant one
            // in this case const Instruction into Instruction.
            const Instruction *inst = dyn_cast<Instruction>(i);
            outs() << "Instruction: " << *inst << "\n";
            if (isLoopInvariant(inst, Loop, invariant_map))
            {
                invariant_map[inst] = true;
                /*
                LLVMContext &C = inst->getContext();
                MDNode *N = MDNode::get(C, MDString::get(C, ""));
                inst->setMetadata("invariant", N);
                */
               outs() << "Loop invariant instruction detected: " << *inst << "\n";
            }
        }
    }
    return PreservedAnalyses::all();
}