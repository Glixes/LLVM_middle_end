//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#define DEBUG

#include "llvm/Transforms/Utils/LocalOpts.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

/**
 * Map associating binary operations with their opposite operation
 * Signed operations are excluded
*/
const std::unordered_map<Instruction::BinaryOps, Instruction::BinaryOps> oppositeOp =
{
  {BinaryOperator::Add, BinaryOperator::Sub},
  {BinaryOperator::Sub, BinaryOperator::Add},
  {BinaryOperator::Mul, BinaryOperator::UDiv},
  {BinaryOperator::UDiv, BinaryOperator::Mul},
  {BinaryOperator::Shl, BinaryOperator::LShr},
  {BinaryOperator::LShr, BinaryOperator::Shl}
};

/**
 * Get a representation of a single variable binary operation in terms of variable and integer constant
 * 
 * @param inst the binary instruction
 * @return a pair of a variable and a constant; if a constant is not present it returns a nullptr in its place, and the variable
 * returned is the first one
 * 
*/
std::pair<Value*, ConstantInt*>* getVarAndConst (Instruction &inst)
{
  // TODO: Add check of instruction type
  Value *val1 = inst.getOperand(0);
  Value *val2 = inst.getOperand(1);
  ConstantInt *CI = dyn_cast<ConstantInt>(val1);
  if ((BinaryOperator::Add || BinaryOperator::Mul) && CI)
  {
    return new std::pair<Value*, ConstantInt*> (val2, CI);
  }
  else
  {
    // if val2 is not castable to ConstantInt the second entity of the pair is nullptr
    return new std::pair<Value*, ConstantInt*> (val1, dyn_cast<ConstantInt>(val2));
  }
  // this should never be reached
  llvm::outs() << "Trollollollol \n";
  return nullptr;
}

/**
 * Get the number of integer constants in the binary instruction
 * 
 * @param inst the binary instruction
 * @return the number of integer constants
*/
size_t getNConstants (Instruction &inst)
{
  ConstantInt *C1 = dyn_cast<ConstantInt>(inst.getOperand(0));
  ConstantInt *C2 = dyn_cast<ConstantInt>(inst.getOperand(1));
  size_t counter = 0;
  if (C1)
    counter++;
  if (C2)
    counter++;
  return counter;
}

/** @brief Compute constant folding optimization on a binary instruction and susbtitute the instruction uses
 * 
 * @param inst the binary instruction
 * @return true if optimized, false otherwise
*/
bool tryConstantFolding (Instruction *inst)
{

  #ifdef  DEBUG
  llvm::outs() << "Entered in function tryConstantFolding\n";
  #endif

  if (!inst)
    return false;

  ConstantInt *C1 = dyn_cast<ConstantInt>(inst->getOperand(0));
  ConstantInt *C2 = dyn_cast<ConstantInt>(inst->getOperand(1));

  if (!C1 || !C2)
    return false;

  #ifdef  DEBUG
  llvm::outs() << "C1 :" << C1 << ",\tC2 :" <<C2 << "\n";
  #endif

  APInt fact1 = C1->getValue();
  APInt fact2 = C2->getValue();

  switch (inst->getOpcode())
  {
    case BinaryOperator::Add:
      if (C1->isZero() || C2->isZero())
        return false;
      fact1 += fact2;
      break;
    
    case BinaryOperator::Sub:
      fact1 -= fact2;
      break;

    case BinaryOperator::Mul:
      fact1 *= fact2;
      break;

    case BinaryOperator::SDiv:
      fact1 = fact1.udiv(fact2);
      break;

    case BinaryOperator::UDiv:
      fact1 = fact1.udiv(fact2);
      break;

    default:
      return false;
  }

  ConstantInt *result = ConstantInt::get(C1->getType(), fact1.getSExtValue());
  ConstantInt *zero = ConstantInt::get(C1->getType(), 0);
  Instruction *addi = BinaryOperator::Create(Instruction::Add, result, zero);

  #ifdef  DEBUG
  llvm::outs() << "Folding done. Result = " << result << "\nSubstituing operation\n";
  #endif

  addi->insertAfter(inst);
  inst->replaceAllUsesWith(addi);

  return true;
}

/** @brief Check the binary instruction for algebraic identity and, in positive cases, replace its uses
 * 
 * @param inst the binary instruction
 * @return true if optimized, false otherwise
*/
bool tryAlgebraicIdentity (Instruction *inst)
{
  #ifdef  DEBUG
  llvm::outs() << "Entered in function tryAlgebraicIdentity\n";
  #endif

  std::pair<Value*, ConstantInt*>* VarAndConst = getVarAndConst(&inst)

  // getVarAndConst can return a ConstantInt in first position. In this case  
  Value* val = VarAndConst.get(0);
  ConstantInt* con = VarAndConst.get(1);
  bool ToReplace = false;


  // We use switch case for future implementation of AlgebraicIdentity not yet implemented (like -(-i))
  switch (inst->getOpcode())
  {
    case BinaryOperator::Add:
    case BinaryOperator::Sub:
    case BinaryOperator::Shl:
    case BinaryOperator::LShr:
      if (con && con->isZero())
        ToReplace = true;
      break;
    case BinaryOperator::Mul:
    case BinaryOperator::UDiv:
    case BinaryOperator::SDiv:
      if (con && con->isOne())
        ToReplace = true;
      break;
  }

/*  if (!C)
    return false;*/

  /*The Value type is necessary in order to include also the Argument objects (representig
  * function's arguments).
  */
  if(ToReplace)
    inst->replaceAllUsesWith(val);
  return ToReplace;
}

/** @brief Check the operation for strength reduction optimiziations
 * In case of multiplication and in case of divisions where the constant is a power of two,
 * a shift is inserted, followed by eventual needed multiplications (to be optimized in the following stages) and subtrations
 * 
 * @param inst the binary instruction
 * @return true if optimized, false otherwise
*/
bool tryStrengthReduction (Instruction *inst)
{

  #ifdef DEBUG
  llvm::outs() << "Entered in function tryStrengthReduction\n";
  #endif

  if (!inst)
    return false;

  std::pair<Value*, ConstantInt*>* VarAndConst = getVarAndConst(&inst);
  Value* val = VarAndConst.get(0);
  ConstantInt* con = VarAndConst.get(1);
  // Negative constants are not handled
  unsigned int shiftVal = con->getValue().ceilLogBase2();
  ConstantInt *shift = ConstantInt::get(con->getType(), shiftVal);

  // Last instruction to be insert
  Instruction* Lastinst = nullptr;
  switch (inst->getOpcode())
  {
      case BinaryOperator::Mul:
      {
        Instruction *shli = BinaryOperator::Create(Instruction::Shl, val, shift);
        shli->insertAfter(inst);
        unsigned int restVal = (1 << shiftVal) - con->getValue().getSExtValue();
        ConstantInt *rest = ConstantInt::get(con->getType(), restVal);

        if (restVal == 0)
        {
          Lastinst = shli;
        }
        else if (restVal == 1)
        {
          Lastinst = BinaryOperator::Create(BinaryOperator::Sub, shli, val);
          Lastinst->insertAfter(shli);
        }
        // if rest is > 1 an intermediate multiplication is needed
        else if (restVal > 1)
        {
          Instruction *muli = BinaryOperator::Create(BinaryOperator::Mul, val, rest);
          muli->insertAfter(shli);
          Lastinst = BinaryOperator::Create(BinaryOperator::Sub, shli, muli);
          Lastinst->insertAfter(muli);
        }
        break;
      }

      case BinaryOperator::UDiv:
      case BinaryOperator::SDiv:
      {
        if (con && con->getValue().isPowerOf2())
        {
          Lastinst = BinaryOperator::Create(Instruction::LShr, val, shift);
          Lastinst->insertAfter(inst);
        }
        break;
      }
  }

  #ifdef DEBUG
  llvm::outs() << "LastInst: " << Lastinst << "\n";
  #endif

  if (!Lastinst)
    #ifdef DEBUG
    llvm::outs() << "No StrengthReduction operations done!\n";
    #endif
    return false;

  inst->replaceAllUsesWith(Lastinst);
  return true;
}

/** @brief Apply Multi Instruction Optimization if possible.
 * 
 * @param o operation examined
 * @return Reference to the operand of the examined operation which is not constant.
*/
bool tryMultiInstructionOpt (Instruction *inst)
{
  #ifdef  DEBUG
  outs() << "Trying to do Multi Instruction\n";
  #endif

  if (!inst)
    return false;
  std::pair<Value*, ConstantInt*>* VarAndConst = getVarAndConst(&inst);
  Value* val = VarAndConst.get(0);
  ConstantInt* con = VarAndConst.get(1);

  if (!con)
    return false;

  for (auto &use : inst->inst->uses())
  {
    Instruction *User = dyn_cast<Instruction>(use.getUser());
    if (!User)
      continue;

    Operation *UserOp = new Operation(*(User));

    #ifdef DEBUG
    outs() << "I'm inside getMultiInstruction, just before the if\n";
    #endif
    if (!UserOp->isValidForOpt() || !inst->hasSameConstant(UserOp) || !inst->isOppositeOp(UserOp))
      continue;
    
    #ifdef DEBUG
    outs() << "I'm inside getMultiInstruction, just before the return\n";
    #endif
    Value *res = dyn_cast<Value>(inst->getOpposite(inst->getFirstConstantInt()));
    use->replaceAllUsesWith(res);
    return true;
  }

  return false;
}

bool runOnBasicBlock(BasicBlock &B) 
{
  bool Transformed = false;

  do 
  {
    Transformed = false;
    for (auto &inst : B) 
    {
      // check for binary operations
      if (!inst.isBinaryOp())
        continue;
      Operation *o = new Operation (inst);

      #ifdef  DEBUG
      outs() << "Instruction: " << inst << "\n";
      #endif
      
      size_t nConstants = o->getNConstants();
      if (nConstants == 0)
        continue;

      Transformed = tryAlgebraicIdentity(o);
      if (Transformed) continue;
      if (nConstants == 2)
      {
        Transformed = getConstantFolding(o);
        if (Transformed) continue;
      }
      Transformed = getMultiInstructionOpt(o);
      if (Transformed) continue;
      #ifdef  DEBUG
      outs() << "Trying to do Strength Reduction\n";
      #endif
      Transformed = tryStrengthReduction(o);
      if (Transformed) continue;
    }
  }
  while (Transformed && false);

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

PreservedAnalyses LocalOpts::run(Module &M, ModuleAnalysisManager &AM) {
  for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
    if (runOnFunction(*Fiter))
      return PreservedAnalyses::none();

  return PreservedAnalyses::all();
}