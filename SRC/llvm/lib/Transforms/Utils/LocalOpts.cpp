//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LocalOpts.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"


using namespace llvm;

bool runOnBasicBlock(BasicBlock &B) {

    /*
      // Preleviamo le prime due istruzioni del BB
      Instruction &Inst1st = *B.begin(), &Inst2nd = *(++B.begin());

      // L'indirizzo della prima istruzione deve essere uguale a quello del 
      // primo operando della seconda istruzione (per costruzione dell'esempio)
      assert(&Inst1st == Inst2nd.getOperand(0));

      // Stampa la prima istruzione
      outs() << "PRIMA ISTRUZIONE: " << Inst1st << "\n";
      // Stampa la prima istruzione come operando
      outs() << "COME OPERANDO: ";
      Inst1st.printAsOperand(outs(), false);
      outs() << "\n";

      // User-->Use-->Value
      outs() << "I MIEI OPERANDI SONO:\n";
      for (auto *Iter = Inst1st.op_begin(); Iter != Inst1st.op_end(); ++Iter) {
        Value *Operand = *Iter;

        if (Argument *Arg = dyn_cast<Argument>(Operand)) {
          outs() << "\t" << *Arg << ": SONO L'ARGOMENTO N. " << Arg->getArgNo() 
            <<" DELLA FUNZIONE " << Arg->getParent()->getName()
                  << "\n";
        }
        if (ConstantInt *C = dyn_cast<ConstantInt>(Operand)) {
          outs() << "\t" << *C << ": SONO UNA COSTANTE INTERA DI VALORE " << C->getValue()
                  << "\n";
        }
      }

      outs() << "LA LISTA DEI MIEI USERS:\n";
      for (auto Iter = Inst1st.user_begin(); Iter != Inst1st.user_end(); ++Iter) {
        outs() << "\t" << *(dyn_cast<Instruction>(*Iter)) << "\n";
      }

      outs() << "E DEI MIEI USI (CHE E' LA STESSA):\n";
      for (auto Iter = Inst1st.use_begin(); Iter != Inst1st.use_end(); ++Iter) {
        outs() << "\t" << *(dyn_cast<Instruction>(Iter->getUser())) << "\n";
      }

      // Manipolazione delle istruzioni
      Instruction *NewInst = BinaryOperator::Create(
          Instruction::Add, Inst1st.getOperand(0), Inst1st.getOperand(0));

      NewInst->insertAfter(&Inst1st);
      // Si possono aggiornare le singole references separatamente?
      // Controlla la documentazione e prova a rispondere.
      Inst1st.replaceAllUsesWith(NewInst);
      
    */
    
    Function *F = B.getParent();
    LLVMContext *Ctx = &F->getContext();

    for (auto iter = B.begin(); iter != B.end(); iter++) {
      Instruction &inst = *iter;
      // check if the instruction is a multiplication
      if (inst.getOpcode() != Instruction::Mul)
        continue;
      Value *Op1 = inst.getOperand(0);
      Value *Op2 = inst.getOperand(1);
      Value *Base = nullptr;
      ConstantInt *constant_int = dyn_cast<ConstantInt>(Op1);
      if (!constant_int) {
        constant_int = dyn_cast<ConstantInt>(Op2);
        if (!constant_int)
          continue;
        else
          Base = Op1;
      }
      else
        Base = Op2;
      // check if the integer shift value is a power of 2, if this is the case the insutruction has to be optimized
      const APInt int_shift_val = constant_int->getValue();
      if (!int_shift_val.isPowerOf2())
        continue;
      // print the instruction to be optimized and its users
      outs() << "Instruction to be optimized: " << inst << "\n";
      outs() << "Users:\n";
      for (auto iter2 = inst.user_begin(); iter2 != inst.user_end(); ++iter2) {
        outs() << "\t" << *(dyn_cast<Instruction>(*iter2)) << "\n";
      }
      // create a Value * with the constant shift value as int 32
      Value *shift_val = ConstantInt::get(llvm::Type::getInt32Ty(*Ctx), int_shift_val.logBase2());
      // create the new instruction
      BinaryOperator *NewInst = BinaryOperator::Create(Instruction::Shl, Base, shift_val);
      // insert it and replace the uses of the original instruction
      NewInst->insertAfter(&inst);
      inst.replaceAllUsesWith(NewInst);
    }
    
    return true;
}

bool runOnFunction(Function &F) {
  bool Transformed = false;

  for (auto Iter = F.begin(); Iter != F.end(); ++Iter) {
    if (runOnBasicBlock(*Iter)) {
      Transformed = true;
    }
  }

  return Transformed;
}


PreservedAnalyses LocalOpts::run(Module &M,
                                      ModuleAnalysisManager &AM) {
  for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
    if (runOnFunction(*Fiter))
      return PreservedAnalyses::none();
  
  return PreservedAnalyses::all();
}

