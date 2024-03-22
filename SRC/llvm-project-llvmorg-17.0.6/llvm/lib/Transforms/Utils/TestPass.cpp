#include "llvm/Transforms/Utils/TestPass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Casting.h"

using namespace llvm;

PreservedAnalyses TestPass::run(Function &F, FunctionAnalysisManager &AM) {

	errs() <<" Questa funzione si chiama "<< F.getName() << "\n";
	errs() <<" Numero argomenti "<< F.arg_size();

	int val = 0;
	for (Instruction *inst = F.begin(); inst != F.end(); inst++){
		
		if (CallInst *call_inst = dyn_cast<CallInst>(inst)){
			++val;
		}
	}
	errs() << "Numero di chiamate a funzione: " << val;

	return PreservedAnalyses::all();
	
}
