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

Operation::Operation(Instruction &inst) : inst(&inst), register1(inst.getOperand(0)),
register2(inst.getOperand(1)), C1(dyn_cast<ConstantInt>(register1)),C2(dyn_cast<ConstantInt>(register2)), 
op(inst.getOpcode()) {}


size_t Operation::getNConstants ()
{
  size_t counter = 0;
  if (C1)
    counter++;
  if (C2)
    counter++;
  return counter;
}

Value* Operation::getOpposite (ConstantInt *C)
{
  if (C == C1)
    return register2;
  else if (C == C2)
    return register1;
  return nullptr;
}

ConstantInt* Operation::getFirstConstantInt ()
{
  return (C1) ? C1 : C2;
}

bool Operation::isOppositeOp (Operation *x)
{
  switch (op)
  {
    case BinaryOperator::Add:
      if (x->op == BinaryOperator::Sub) return true;
      break;
    
    case BinaryOperator::Sub:
      if (x->op == BinaryOperator::Add) return true;
      break;

    case BinaryOperator::Mul:
      if (x->op == BinaryOperator::UDiv ||
          x->op == BinaryOperator::SDiv) return true;
      break;

    case BinaryOperator::SDiv:
      if (x->op == BinaryOperator::Mul) return true;
      break;

    case BinaryOperator::UDiv:
      if (x->op == BinaryOperator::Mul) return true;
      break;

    case BinaryOperator::Shl:
      if (x->op == BinaryOperator::LShr) return true;
      break;

    case BinaryOperator::LShr:
      if (x->op == BinaryOperator::Shl) return true;
      break;
  }
  return false;
}

Instruction* Operation::getRegThatIsResult (Operation *o)
{
  Value *res = nullptr;

  if (inst == o->register1 || inst == o->register2)
    res = getOpposite(getFirstConstantInt());

  return dyn_cast_if_present<Instruction> (res);
}

bool Operation::isValidForOpt()
{
  unsigned n_const = Operation::getNConstants();
  if (n_const < 1)
    return false;
  if (op == BinaryOperator::Sub || op == BinaryOperator::SDiv || op == BinaryOperator::UDiv)
    return (!C1? true : false);
  return false;
}

/** @brief Compute constant folding optimization.
 * 
 * @param o operation examined
 * @return Add instruction containing the result as first operand, and 0 as second operand.
*/
Instruction* getConstantFolding (Operation *o)
{
  APInt fact1 = o->C1->getValue();
  APInt fact2 = o->C2->getValue();

  switch (o->op)
  {
    case BinaryOperator::Add:
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

    case BinaryOperator::Shl:
      fact1 = fact1<<=fact2;
      break;

    case BinaryOperator::LShr:
      fact1 = fact1.lshr(fact2);
      break;

    default:
      return nullptr;
  }

  ConstantInt *result = ConstantInt::get(o->C1->getType(), fact1.getSExtValue());
  ConstantInt *zero = ConstantInt::get(o->C1->getType(), 0);
  Instruction *addi = BinaryOperator::Create(Instruction::Add, result, zero);
  addi->insertAfter(o->inst);
  return addi;
}

/** @brief Check the operation for algebraic identity and, in positive cases, return the instruction to replace
 * 
 * @param o operation examined
 * @return Value containing the intruction to replace, nullptr otherwise
*/
Value* getAlgebraicIdentity (Operation *o)
{
  ConstantInt* C = nullptr;
  switch (o->op)
  {
    case BinaryOperator::Add:
      if (o->C1 && o->C1->isZero())
        C = o->C1;
        LLVM_FALLTHROUGH;
    case BinaryOperator::Sub:
    case BinaryOperator::Shl:
    case BinaryOperator::LShr:
      if (o->C2 && o->C2->isZero())
        C = o->C2;
      break;

    case BinaryOperator::Mul:
      if (o->C1 && o->C1->isOne())
        C = o->C1;
        LLVM_FALLTHROUGH;
    case BinaryOperator::UDiv:
    case BinaryOperator::SDiv:
      if (o->C2 && o->C2->isOne())
        C = o->C2;
      break;
  }

  return (C) ? o->getOpposite(C) : nullptr;
}

/** @brief Check the operation for strength reduction optimiziations
 * In case of multiplication and in case of divisions where the constant is a power of two,
 * a shift is inserted, followed by eventual needed multiplications (to be optimized in the following stages) and subctrations
 * 
 * @param o operation examined
 * @return the last instruction inserted, nullptr otherwise
*/
Instruction* getStrengthReduction (Operation *o)
{
  ConstantInt *C = o->getFirstConstantInt();
  // Negative constants are not handled
  unsigned int shiftVal = C->getValue().ceilLogBase2();
  ConstantInt *shift = ConstantInt::get(C->getType(), shiftVal);

  Instruction* newinst = nullptr;
  switch (o->op)
  {
      case BinaryOperator::Mul:
      {
        Instruction *shli = BinaryOperator::Create(Instruction::Shl, o->getOpposite(C), shift);
        shli->insertAfter(o->inst);
        unsigned int restVal = (1 << shiftVal) - C->getValue().getSExtValue();
        ConstantInt *rest = ConstantInt::get(C->getType(), restVal);
        if (restVal == 0)
        {
          newinst = shli;
        }
        else if (restVal == 1)
        {
          newinst = BinaryOperator::Create(BinaryOperator::Sub, shli, o->getOpposite(C));
          newinst->insertAfter(shli);
        }
        // if rest is > 1 an intemermediate multiplication is needed
        else if (restVal > 1)
        {
          Instruction *muli = BinaryOperator::Create(BinaryOperator::Mul, o->getOpposite(C), rest);
          muli->insertAfter(shli);
          newinst = BinaryOperator::Create(BinaryOperator::Sub, shli, muli);
          newinst->insertAfter(muli);
        }
        break;
      }

      case BinaryOperator::UDiv:
      case BinaryOperator::SDiv:
      {
        if (C == o->C2 && C->getValue().isPowerOf2())
        {
          newinst = BinaryOperator::Create(Instruction::LShr, o->getOpposite(C), shift);
          newinst->insertAfter(o->inst);
        }
        break;
      }
  }
  return newinst;
}

/** @brief Apply Multi Instruction Optimization if possible.
 * 
 * @param o2 operation examined
 * @param constantsLog hash map containing 
*/
Instruction* getMultiInstructionOpt (Operation *o2, std::unordered_map<ConstantInt*, std::vector<Operation*>> &constantsLog)
{
  ConstantInt *C = o2->getFirstConstantInt();
  if (!o2->isValidForOpt())
    return nullptr;

  for (Operation *o1 : constantsLog[C])
  {
    if (!o1->isValidForOpt())
      continue;
    
    if (o2->isOppositeOp(o1))
    {
      return o1->getRegThatIsResult(o2);
    }
  }
  return nullptr;
}

bool runOnBasicBlock(BasicBlock &B) 
{
  std::unordered_map<ConstantInt*, std::vector<Operation*>> constantsLog;
  bool optimizedLastCycle = false;

  do 
  {
    optimizedLastCycle = false;
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

      if (o->C1) constantsLog[o->C1].push_back(o);
      if (o->C2) constantsLog[o->C2].push_back(o);

      /* Optimized instruction.
      * The Value type is necessary in order to include also the Argument objects (representig
      * function's arguments).
      */
      #ifdef  DEBUG
      outs() << "Trying to do AlgebriaicIdentity\n";
      #endif
      Value *i = getAlgebraicIdentity(o);
      // handle infinite loop
      //if (!i && nConstants == 2) i = getConstantFolding(o);
      if (!i && nConstants == 2)
      {
        #ifdef  DEBUG
        outs() << "Trying to do ConstantFolding\n";
        #endif
        i = getConstantFolding(o);
      }
      //if (!i) i = getMultiInstructionOpt(o, constantsLog);
      if (!i)
      {
        #ifdef  DEBUG
        outs() << "Trying to do Multi Instruction\n";
        #endif
        i = getMultiInstructionOpt(o, constantsLog);
      }
      //if (!i) i = getStrengthReduction(o);
      if (!i)
      {
        #ifdef  DEBUG
        outs() << "Trying to do Strength Reduction\n";
        #endif
        i = getStrengthReduction(o);
      }

      // replace the non-optimized instruction uses with the optimized ones
      if (i)
      {
        inst.replaceAllUsesWith(i);
        optimizedLastCycle = true;
      }
    }
  }
  while (optimizedLastCycle && false);

  constantsLog.clear();
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