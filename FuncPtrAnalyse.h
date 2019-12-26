#include <llvm/Pass.h>
#include <map>
#include <set>
#include <vector>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>


///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 3
using namespace llvm;

class FuncPtrPass : public ModulePass {
public:
    static char ID; // Pass identification, replacement for typeid
    FuncPtrPass() : ModulePass(ID) {}

    typedef std::set<Value*> FuncPtrSet;
    typedef std::map<Value*, FuncPtrSet> Env;

    std::map<BasicBlock*, Env> envs;
    Env *_currEnv;
    std::map<Function *, std::map<Instruction *, Env>> argsEnv; // Record function arguments which is a pointer
    Env returned;  // Record the values each func may return.

    std::map<Function *, std::map<Instruction *, Env>> globalEnvPerFunc; // A global record of FuncPtrSetMap at each function and its callsite
    std::map<Function *, Env> dirtyEnvPerFunc;
    std::map<Instruction *, Value *> allocated;  // Record the value created by allocation instructions.
    std::set<Value *> dirtyValues; // during a function...

    void markDirty(Value *p)
    {
        dirtyValues.insert(p);
    }

    #define currEnv (*_currEnv)

    bool runOnModule(Module &M) override;

    bool iterate(Module &M);

    Env meet(BasicBlock *bb);

    bool dispatchInst(Instruction &inst);

    bool visitPhiNode(PHINode *phiNode);

    bool visitCall(CallInst *callInst);

    bool visitAlloc(AllocaInst *allocaInst);

    bool visitGetElementPtr(GetElementPtrInst* getElementPtrInst);

    bool visitLoad(LoadInst *loadInst);

    bool visitStore(StoreInst *storeInst);

    bool visitReturn(ReturnInst *returnInst);

    bool visitBitcast(BitCastInst *bitCastInst);

    bool visitMemCopy(MemCpyInst *copyInst);

    Value *createAllocValue(Instruction *allloc);

    Env passArgs(Function *func);

    bool isFunctionPointer(Type *type);

    FuncPtrSet wrappedPtrSet(Value *value);

    bool setUnion(FuncPtrSet &dst, const FuncPtrSet &src);

    bool isLLVMBuiltIn(CallInst *callInst);

    void envUnion(Env &dst, const Env &src);

    void updateEnv(Env &dst, const Env &src);

    // Debug tools

    void printSet(const FuncPtrSet &s);

    void printEnv(Env &env);

    void printCalls(Module &M);

};
