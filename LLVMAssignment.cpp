//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/IR/CFG.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/ToolOutputFile.h>
#include <sstream>

#if LLVM_VERSION_MAJOR >= 4
#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#else
#include <llvm/Bitcode/ReaderWriter.h>
#endif

#include <llvm/Transforms/Scalar.h>

#include "Liveness.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;
#if LLVM_VERSION_MAJOR >= 4
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }
#endif

/* In LLVM 5.0, when  -O0 passed to clang , the functions generated with clang
 * will have optnone attribute which would lead to some transform passes
 * disabled, like mem2reg.
 */
#if LLVM_VERSION_MAJOR == 5
struct EnableFunctionOptPass : public FunctionPass {
  static char ID;
  EnableFunctionOptPass() : FunctionPass(ID) {}
  bool runOnFunction(Function &F) override {
    if (F.hasFnAttribute(Attribute::OptimizeNone)) {
      F.removeFnAttr(Attribute::OptimizeNone);
    }
    return true;
  }
};

char EnableFunctionOptPass::ID = 0;
#endif

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 3
struct FuncPtrPass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  FuncPtrPass() : ModulePass(ID) {}
  typedef std::set<Value *> FuncPtrSet;
  typedef std::map<Value *, FuncPtrSet> Env;
  Env *_currEnv;
  std::map<Function *, std::map<Instruction *, Env>> argsEnv;
  std::map<Function *, std::map<Instruction *, Env>> globalEnvPerFunc;
  std::map<Function *, Env> dirtyEnvPerFunc;
  std::map<BasicBlock *, Env> envs;
  std::map<Instruction *, Value *> allocated;

  Env returned;

  bool runOnModule(Module &M) override {
    errs() << "Hello: ";
    errs().write_escaped(M.getName()) << '\n';
    M.dump();
    errs() << "------------------------------\n";

    while (iterate(M))
      ;

    printCalls(M);

    return false;
  }

  bool iterate(Module &module) {

    auto oldArgsEnv = argsEnv;
    auto oldReturned = returned;
    auto oldHeap = globalEnvPerFunc;
    auto oldDirty = dirtyEnvPerFunc;

    for (Function &func : module.getFunctionList()) {
      for (BasicBlock &bb : func) {
        Env in, out;

        if (&bb == &func.getEntryBlock())
          // If instruction is the 1st instruction of a function, pointer set
          // should come from function arguments
          in = passArgs(&func);
        else
          // pointer set comes from predecessors
          in = meet(&bb);

        for (const auto &it : globalEnvPerFunc[&func])
          envUnion(in, it.second);

        out = in;

        _currEnv = &out;
        for (auto &inst : bb) {
          dispatchInst(inst);
        }

        if (out != envs[&bb]) {
          envs[&bb] = out;
        }
      }
    }

    // if changed, this function will be invoke again
    return argsEnv != oldArgsEnv || returned != oldReturned ||
           globalEnvPerFunc != oldHeap || dirtyEnvPerFunc != oldDirty;
  }

  Env meet(BasicBlock *bb) {
    Env in;
    for (auto *p : predecessors(bb)) {
      for (auto pair : envs[p]) {
        setUnion(in[pair.first], pair.second);
      }
    }
    return in;
  }

  bool dispatchInst(Instruction &inst) {
    if (auto casted = dyn_cast<PHINode>(&inst))
      return visitPhiNode(casted);

    if (auto casted = dyn_cast<CallInst>(&inst))
      return visitCall(casted);

    if (auto casted = dyn_cast<AllocaInst>(&inst))
      return visitAlloc(casted);

    if (auto casted = dyn_cast<GetElementPtrInst>(&inst))
      return visitGetElementPtr(casted);

    if (auto load = dyn_cast<LoadInst>(&inst))
      return visitLoad(load);

    if (auto store = dyn_cast<StoreInst>(&inst))
      return visitStore(store);

    if (auto casted = dyn_cast<ReturnInst>(&inst))
      return visitReturn(casted);

    if (auto bit = dyn_cast<BitCastInst>(&inst))
      return visitBitcast(bit);

    return false;
  }

  bool visitPhiNode(PHINode *phiNode) {
    for (unsigned incoming_index = 0, e = phiNode->getNumIncomingValues();
         incoming_index != e; incoming_index++) {
      Value *inVal = phiNode->getIncomingValue(incoming_index);
      if (dyn_cast<Function>(inVal))
        setUnion((*_currEnv)[phiNode], wrappedPtrSet(inVal));
      else
        setUnion((*_currEnv)[phiNode], (*_currEnv)[inVal]);
    }
    return false;
  }

  bool visitCall(CallInst *callInst) {
    if (isLLVMBuiltIn(callInst)) {
      if (auto copyInst = dyn_cast<MemCpyInst>(callInst))
        return visitMemCopy(copyInst);
      else
        return false;
    }

    bool updated = false;

    FuncPtrSet possible_func_ptr_set;

    if (auto *func = callInst->getCalledFunction()) {
      possible_func_ptr_set.insert(callInst->getCalledFunction());
      if (func->getName() == "malloc") {
        if ((*_currEnv)[callInst].empty()) {
          Value *p = createAllocValue(callInst);
          (*_currEnv)[callInst].insert(p);
          updated = true;
        }
      }
    } else {
      auto called_value = callInst->getCalledValue();
      possible_func_ptr_set = (*_currEnv)[called_value];
    }

    Env dirtyEnv;
    for (auto value : possible_func_ptr_set) {
      auto func = dyn_cast<Function>(value);
      if (!func)
        continue;

      // update call pointer set with return value set
      if (callInst->getType()->isPointerTy()) {
        auto updated_call_inst =
            setUnion((*_currEnv)[callInst], returned[func]);
        updated |= updated_call_inst;
      }

      // function callsites and arguments
      unsigned arg_index = 0;
      for (auto &parameter : func->args()) {
        if (parameter.getType()->isPointerTy()) {
          auto arg = callInst->getOperand(arg_index);
          argsEnv[func][callInst][&parameter] = wrappedPtrSet(arg);
        }
        arg_index++;
      }

      // Pass current env as callee's env.
      auto &myOldProvide = globalEnvPerFunc[func][callInst];
      if (myOldProvide != (*_currEnv)) {
        myOldProvide.clear();
        myOldProvide = (*_currEnv);
      } else {
        // Fetch dirty data from this called function
        envUnion(dirtyEnv, dirtyEnvPerFunc[func]);
      }
    }

    for (auto &kv : globalEnvPerFunc) {
      if (possible_func_ptr_set.count(kv.first) == 0 &&
          kv.second.count(callInst) != 0) {
        kv.second[callInst].clear();
      }
    }

    updateEnv((*_currEnv), dirtyEnv);

    return updated;
  }

  Value *createAllocValue(Instruction *alloc) {
    if (allocated.count(alloc)) {
      return allocated[alloc];
    } else {
      char name[20];
      Value *v = new AllocaInst(
          IntegerType::get(alloc->getModule()->getContext(), 32), 10, name);
      allocated[alloc] = v;
      return v;
    }
  }

  bool visitAlloc(AllocaInst *allocaInst) {
    if ((*_currEnv).count(allocaInst) == 0) {
      Value *p = createAllocValue(allocaInst);
      (*_currEnv)[p];
      (*_currEnv)[allocaInst].insert(p);
      return true;
    } else {
      return false;
    }
  }

  bool visitGetElementPtr(GetElementPtrInst *getElementPtrInst) {
    bool updated = false;
    Value *ptr = getElementPtrInst->getOperand(0);
    updated = setUnion((*_currEnv)[getElementPtrInst], (*_currEnv)[ptr]);
    return updated;
  }

  bool visitLoad(LoadInst *loadInst) {
    bool updated = false;
    Value *src = loadInst->getOperand(0);
    for (auto p : (*_currEnv)[src]) {
      updated = setUnion((*_currEnv)[loadInst], (*_currEnv)[p]);
    }
    return updated;
  }

  bool visitStore(StoreInst *storeInst) {
    bool updated = false;
    Value *src = storeInst->getOperand(0);
    Value *dst = storeInst->getOperand(1);
    for (auto p : (*_currEnv)[dst]) {
      (*_currEnv)[p] = wrappedPtrSet(src);
    }

    return updated;
  }

  bool visitReturn(ReturnInst *returnInst) {
    Function *func = returnInst->getParent()->getParent();

    Env heap;
    for (const auto &it : globalEnvPerFunc[func]) {
      envUnion(heap, it.second);
    }

    bool hasPointerArgs = false;
    for (auto &arg : func->args()) {
      if (arg.getType()->isPointerTy()) {
        hasPointerArgs = true;
        break;
      }
    }
    if (hasPointerArgs) {
      if (dirtyEnvPerFunc[func] != (*_currEnv)) {
        dirtyEnvPerFunc[func] = (*_currEnv);
      }
    } else {
      dirtyEnvPerFunc[func].clear();
    }

    // Update return value set.
    auto value = returnInst->getReturnValue();
    if (value == nullptr || !value->getType()->isPointerTy()) {
      return false;
    }

    return setUnion(returned[func], wrappedPtrSet(value));
  }

  bool visitBitcast(BitCastInst *bitCastInst) {
    Value *ope = bitCastInst->getOperand(0);
    return setUnion((*_currEnv)[bitCastInst], (*_currEnv)[ope]);
  }

  Env passArgs(Function *func) {
    Env in;
    auto &argsPerCallSite = argsEnv[func];
    for (auto &it : argsPerCallSite) {
      for (auto &arg : func->args()) {
        if (arg.getType()->isPointerTy()) {
          setUnion(in[&arg], it.second[&arg]);
        }
      }
    }
    return in;
  }

  void envUnion(FuncPtrPass::Env &dst,
                             const FuncPtrPass::Env &src) {
    for (auto &pair : src) {
      setUnion(dst[pair.first], pair.second);
    }
  }

  void updateEnv(FuncPtrPass::Env &dst,
                              const FuncPtrPass::Env &src) {
    // For each key in dst, if src has this key, override the content.
    for (auto &pair : dst) {
      if (src.count(pair.first)) {
        const auto &set = *src.find(pair.first);
        if (set.second != pair.second) {
          dst[pair.first] = set.second;
        }
      }
    }
  }

  bool visitMemCopy(MemCpyInst *copyInst) {
    auto src = copyInst->getSource();
    auto dst = copyInst->getDest();
    for (auto d : (*_currEnv)[dst]) {
      (*_currEnv)[d].clear();
      for (auto s : (*_currEnv)[src]) {
        setUnion((*_currEnv)[d], wrappedPtrSet(s));
      }
    }
    return false;
  }

  bool isFunctionPointer(Type *type) {
    if (!type->isPointerTy()) {
      return false;
    }
    auto pointee = type->getPointerElementType();
    return pointee->isFunctionTy();
  }

  FuncPtrSet wrappedPtrSet(Value *value) {
    if (isa<Function>(value)) {
      FuncPtrSet fPtrSet;
      fPtrSet.insert(value);
      return fPtrSet;
    } else {
      return (*_currEnv)[value];
    }
  }

  bool setUnion(FuncPtrSet &dst,
                             const FuncPtrSet &src) {
    bool updated = false;
    for (const auto it : src) {
      bool inserted;
      std::tie(std::ignore, inserted) = dst.insert(it);
      updated |= inserted;
    }
    return updated;
  }

  bool isLLVMBuiltIn(CallInst *callInst) {
    return isa<DbgValueInst>(callInst) || isa<DbgDeclareInst>(callInst) ||
           isa<MemSetInst>(callInst) || isa<MemCpyInst>(callInst);
  }

  void printEnv(Env &env) {
    for (auto &pair : env) {
      Value *key = pair.first;
      FuncPtrSet &set = pair.second;
      if (key->getName() == "") {
        llvm::errs() << key->getValueID() << ": ";
      } else {
        llvm::errs() << key->getName() << ": ";
      }

      std::stringstream ss;
      std::string sep;
      ss << "{ ";
      for (auto p : set) {
        ss << sep << p->getName().str();
        sep = ", ";
      }
      ss << " }\n";
      llvm::errs() << ss.str();
    }
  }

  void printSet(const FuncPtrSet &s) {
    std::stringstream ss;
    std::string sep = "";
    ss << "{ ";
    for (auto p : s) {
      ss << sep << p->getName().str();
      sep = ", ";
    }
    ss << " }";
  }

  void printCalls(Module &module) {
    unsigned last_line = 0;
    bool first_in_current_line = true;
    bool first_line = true;
    for (auto &function : module.getFunctionList()) {
      for (auto &bb : function) {
        _currEnv = &envs[&bb];
        for (auto &inst : bb) {
          unsigned null_count = 0, pointer_count = 0;
          if (auto callInst = dyn_cast<CallInst>(&inst)) {
            if (isLLVMBuiltIn(callInst)) {
              continue;
            }
            auto calledValue = callInst->getCalledValue();
            FuncPtrSet possible_func_ptr_set = wrappedPtrSet(calledValue);
            MDNode *metadata = callInst->getMetadata(0);
            if (!metadata) {
              errs() << "No meta data found for " << *callInst;
              continue;
            }
            DILocation *debugLocation = dyn_cast<DILocation>(metadata);
            if (!debugLocation) {
              errs() << "No debug location found for " << *callInst;
              continue;
            }
            unsigned current_line = debugLocation->getLine();
            if (last_line != current_line) {
              first_in_current_line = true;
              if (!first_line) {
                errs() << "\n";
              } else {
                first_line = false;
              }
              errs() << current_line << " : ";
            }
            for (auto value : possible_func_ptr_set) {
              auto func = dyn_cast<Function>(value);
              if (!func || func->getName() == "") {
                null_count++;
                continue;
              }
              pointer_count++;
              if (!first_in_current_line) {
                errs() << ", ";
              } else {
                first_in_current_line = false;
              }
              errs() << func->getName();
            }
            last_line = current_line;
          }
        }
      }
    }
  }
};

char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass",
                                   "Print function call instruction");

char Liveness::ID = 0;
static RegisterPass<Liveness> Y("liveness", "Liveness Dataflow Analysis");

static cl::opt<std::string>
    InputFilename(cl::Positional, cl::desc("<filename>.bc"), cl::init(""));

int main(int argc, char **argv) {
  LLVMContext &Context = getGlobalContext();
  SMDiagnostic Err;
  // Parse the command line to read the Inputfilename
  cl::ParseCommandLineOptions(
      argc, argv, "FuncPtrPass \n My first LLVM too which does not do much.\n");

  // Load the input module
  std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
  if (!M) {
    Err.print(argv[0], errs());
    return 1;
  }

  llvm::legacy::PassManager Passes;
#if LLVM_VERSION_MAJOR == 5
  Passes.add(new EnableFunctionOptPass());
#endif
  /// Transform it to SSA
  Passes.add(llvm::createPromoteMemoryToRegisterPass());

  /// Your pass to print Function and Call Instructions
  // Passes.add(new Liveness());
  Passes.add(new FuncPtrPass());
  Passes.run(*M.get());
#ifndef NDEBUG
  system("pause");
#endif
}
