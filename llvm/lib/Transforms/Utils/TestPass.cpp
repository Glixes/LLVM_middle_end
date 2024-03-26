#include "llvm/Transforms/Utils/TestPass.h"
#include "llvm/IR/Instructions.h"
using namespace llvm;

PreservedAnalyses TestPass::run(Module &M,ModuleAnalysisManager &AM) {
    errs() << "Called Test Pass - Module version" << "\n";
    for (auto iter = M.begin(); iter != M.end(); iter++) {
        Function &F = *iter;
        errs() << "Function name: " << F.getName() << "\n";
        unsigned arg_count = F.arg_size();
        bool isvararg = F.isVarArg();
        errs() << "Number of arguments: " << arg_count << (isvararg? "+*":"") << "\n";
        unsigned block_count = 0, instruction_count = 0, call_count = 0;
        for (auto iter2 = F.begin(); iter2 != F.end(); iter2++) {
            block_count++;
            BasicBlock &BB = *iter2;
            for (auto iter3 = BB.begin(); iter3 != BB.end(); iter3++) {
                instruction_count++;
                Instruction &I = *iter3;
                if (CallInst *call_inst = dyn_cast<CallInst>(&I))
                    call_count++;
                }
        }
        errs() << "Number of basic blocks: " << block_count << "\n";
        errs() << "Number of instructions: " << instruction_count << "\n";
        errs() << "Number of function calls: " << call_count << "\n";
    }
    
    return PreservedAnalyses::all();
}
