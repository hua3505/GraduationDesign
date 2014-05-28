//===-- Executor.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#define OS_GLOBALS
#include "record_monitor.h"
#include "Common.h"

#include "Executor.h"

#include "PTree.h"
#include "Context.h"
#include "CoreStats.h"
#include "ExternalDispatcher.h"
#include "ImpliedValue.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "PTree.h"
#include "Searcher.h"
#include "SeedInfo.h"
#include "SpecialFunctionHandler.h"
#include "StatsTracker.h"
#include "TimingSolver.h"
#include "UserSearcher.h"
#include "../Solver/SolverStats.h"

#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Interpreter.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/CommandLine.h"
#include "klee/Common.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprSMTLIBLetPrinter.h"
#include "klee/util/ExprUtil.h"
#include "klee/util/GetElementPtrTypeIterator.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/FloatEvaluation.h"
#include "klee/Internal/System/Time.h"

#include "llvm/Attributes.h"
#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(2, 7)
#include "llvm/LLVMContext.h"
#endif
#include "llvm/Module.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#if LLVM_VERSION_CODE < LLVM_VERSION(2, 9)
#include "llvm/System/Process.h"
#else
#include "llvm/Support/Process.h"
#endif
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
#include "llvm/Target/TargetData.h"
#else
#include "llvm/DataLayout.h"
#endif

#include <cassert>
#include <algorithm>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>

#include <sys/mman.h>

#include <errno.h>
#include <cxxabi.h>

/*------------start----------------*/
/* add by wanqizhi*/
#include "ClientAsynchronous.h"
#include "Global.h"
#include "FunLineRange.h"
#include "LabelInformation.h"
#include "InitDataStruct.h"
///cc,add for cout
using namespace std;

//extern int main1();
/*------------end----------------*/

/* hlm */
#include "get_execution_info.h"
#include "LLNum.h"
extern exePthreadInfo* head;
extern exePthreadInfo* current;
extern exePthreadInfo* pre;
using namespace llvm;
using namespace klee;

namespace {
cl::opt<bool> DumpStatesOnHalt("dump-states-on-halt", cl::init(true),
		cl::desc(
				"Dump test cases for all active states on exit (default=on)"));

cl::opt<bool> NoPreferCex("no-prefer-cex", cl::init(false));

cl::opt<bool> UseAsmAddresses("use-asm-addresses", cl::init(false));

cl::opt<bool> RandomizeFork("randomize-fork", cl::init(false),
		cl::desc(
				"Randomly swap the true and false states on a fork (default=off)"));

cl::opt<bool> AllowExternalSymCalls("allow-external-sym-calls", cl::init(false),
		cl::desc(
				"Allow calls with symbolic arguments to external functions.  This concretizes the symbolic arguments.  (default=off)"));

cl::opt<bool> DebugPrintInstructions("debug-print-instructions",
		cl::desc("Print instructions during execution."));

cl::opt<bool> DebugCheckForImpliedValues("debug-check-for-implied-values");

cl::opt<bool> SimplifySymIndices("simplify-sym-indices", cl::init(false));

cl::opt<unsigned> MaxSymArraySize("max-sym-array-size", cl::init(0));

cl::opt<bool> SuppressExternalWarnings("suppress-external-warnings");

cl::opt<bool> AllExternalWarnings("all-external-warnings");

cl::opt<bool> OnlyOutputStatesCoveringNew("only-output-states-covering-new",
		cl::init(false),
		cl::desc("Only output test cases covering new code."));

cl::opt<bool> EmitAllErrors("emit-all-errors", cl::init(false),
		cl::desc(
				"Generate tests cases for all errors "
						"(default=off, i.e. one per (error,instruction) pair)"));

cl::opt<bool> NoExternals("no-externals",
		cl::desc("Do not allow external function calls (default=off)"));

cl::opt<bool> AlwaysOutputSeeds("always-output-seeds", cl::init(true));

cl::opt<bool> OnlyReplaySeeds("only-replay-seeds",
		cl::desc("Discard states that do not have a seed."));

cl::opt<bool> OnlySeed("only-seed",
		cl::desc(
				"Stop execution after seeding is done without doing regular search."));

cl::opt<bool> AllowSeedExtension("allow-seed-extension",
		cl::desc(
				"Allow extra (unbound) values to become symbolic during seeding."));

cl::opt<bool> ZeroSeedExtension("zero-seed-extension");

cl::opt<bool> AllowSeedTruncation("allow-seed-truncation",
		cl::desc("Allow smaller buffers than in seeds."));

cl::opt<bool> NamedSeedMatching("named-seed-matching",
		cl::desc("Use names to match symbolic objects to inputs."));

cl::opt<double> MaxStaticForkPct("max-static-fork-pct", cl::init(1.));
cl::opt<double> MaxStaticSolvePct("max-static-solve-pct", cl::init(1.));
cl::opt<double> MaxStaticCPForkPct("max-static-cpfork-pct", cl::init(1.));
cl::opt<double> MaxStaticCPSolvePct("max-static-cpsolve-pct", cl::init(1.));

cl::opt<double> MaxInstructionTime("max-instruction-time",
		cl::desc(
				"Only allow a single instruction to take this much time (default=0s (off)). Enables --use-forked-stp"),
		cl::init(0));

cl::opt<double> SeedTime("seed-time",
		cl::desc(
				"Amount of time to dedicate to seeds, before normal search (default=0 (off))"),
		cl::init(0));

cl::opt<unsigned int> StopAfterNInstructions("stop-after-n-instructions",
		cl::desc(
				"Stop execution after specified number of instructions (default=0 (off))"),
		cl::init(0));

cl::opt<unsigned> MaxForks("max-forks",
		cl::desc("Only fork this many times (default=-1 (off))"),
		cl::init(~0u));

cl::opt<unsigned> MaxDepth("max-depth",
		cl::desc(
				"Only allow this many symbolic branches (default=0 (off))"),
		cl::init(0));

cl::opt<unsigned> MaxMemory("max-memory",
		cl::desc(
				"Refuse to fork when above this amount of memory (in MB, default=2000)"),
		cl::init(2000));

cl::opt<bool> MaxMemoryInhibit("max-memory-inhibit",
		cl::desc(
				"Inhibit forking at memory cap (vs. random terminate) (default=on)"),
		cl::init(true));

cl::opt<bool> UseForkedSTP("use-forked-stp",
		cl::desc("Run STP in a forked process (default=off)"));

cl::opt<bool> STPOptimizeDivides("stp-optimize-divides",
		cl::desc(
				"Optimize constant divides into add/shift/multiplies before passing to STP (default=on)"),
		cl::init(true));

}

namespace klee {
RNG theRNG;
}

int Executor::createnodeId = 0;

///cc,return value for pthread functions
void Executor::return_value_handle(ExecutionState &state, int value) {
	KInstIterator kcaller = state.prevPC;
	Instruction *caller = kcaller ? kcaller->inst : 0;
	ref<Expr> result = ConstantExpr::alloc(value, Expr::Int32);

	LLVM_TYPE_Q
	Type *t = caller->getType();
	if (t != Type::getVoidTy(getGlobalContext())) {
		// may need to do coercion due to bitcasts
		Expr::Width from = result->getWidth();
		Expr::Width to = getWidthForLLVMType(t);

		if (from != to) {
			CallSite cs = (
					isa<InvokeInst>(caller) ?
							CallSite(cast<InvokeInst>(caller)) :
							CallSite(cast<CallInst>(caller)));

			// XXX need to check other param attrs ?
			if (cs.paramHasAttr(0, llvm::Attribute::SExt)) {
				result = SExtExpr::create(result, to);
			} else {
				result = ZExtExpr::create(result, to);
			}
		}
		bindLocal(kcaller, state, result);
	}
}
void Executor::call_pthread_create(ExecutionState &state, KInstruction* ki,
		Instruction* i, unsigned numArgs, Value* fp, Function* f,
		std::vector<ref<Expr> > &arguments) {
	if (isMonitor) {
		int pathId = state.pathId;
		int threadId = 0;
		//找到是那一条路径下的执行信息
		struct ExecutionImage *ei = NULL;
		for (std::set<ExecutionImage*>::iterator it =
				executionImageList.begin(), ie =
				executionImageList.end(); it != ie; it++) {
			ei = *it;
			if (ei->pathId == pathId) {
				break;
			}
		}
		assert((ei != NULL) && ("路径拷贝监控信息出错！"));

		struct exePthreadInfo *p = ei->head;
		while (p) {
			if ((p->type == 1) && (p->exec == 0)
					&& (state.pthreadId == p->threadId)) {
				threadId = p->newPthreadId;
				break;
			}
			p = p->next;
		}

		if (threadId != 0) {
//			printf("AAA\n");
//			printf("state.pthreadId=%d\n", state.pthreadId);
//			printf("threadId= %d\n", threadId);
			p->exec = 1;
			uint64_t val = 0;
			for (unsigned j = 0; j < numArgs; ++j) {

				ConstantExpr *CE = dyn_cast<ConstantExpr>(
						eval(ki, j + 1, state).value);

				if (j == 2) {
					val = CE->getZExtValue(); //把线程调用的函数名取出
				} else if (j == 3) {
					arguments.push_back(eval(ki, j + 1, state).value); //把调用函数时的参数取出
				}
			}

			//获得其线程标识符
			ref<Expr> idExpr = eval(ki, 1, state).value;
			//std::cout << "idExpr=" << idExpr << std::endl;
			ConstantExpr *CF = dyn_cast<ConstantExpr>(idExpr);
			int threadIdentify = CF->getZExtValue();
			//	std::cout << "threadAddr=" << threadIdentify << std::endl;

			uint64_t addr = 0;
			std::map<llvm::Function*, KFunction*>::const_iterator map_it =
					kmodule->functionMap.begin();

			while (map_it != kmodule->functionMap.end()) {
				addr = (uint64_t) map_it->first;
				if (val == addr) {

					ExecutionState *continueState, *newState;
					++stats::forks; //stats是state的链表，forks是state的个数
					continueState = &state;
					newState = state.branch();
					//newState->pthreadId = ExecutionState::createPthreadId; //产生新的线程号，但不产生新的路径号
					//ExecutionState::createPthreadId++;

					newState->pthreadId = threadId; //产生新的线程号，但不产生新的路径号

					newState->isMain = 0; //非主线程
					newState->sumFunc = 1; //次线程的函数只调用了一层
					//hlm
					newState->snapShotList.clear();
					PthreadInfo *threadCon = new PthreadInfo(
							threadIdentify, newState->pthreadId);
					threadCon->isAlives.insert(
							pair<int, int>(newState->pathId, 1));
					threadList.push_back(threadCon);

					//hlm
					addedStates.insert(newState);

					delete newState->exeInfo;
					newState->exeInfo = new ExecutionInfo(); //创建线程的执行信息

					KFunction *kf = map_it->second; //取出f相对应函数

					newState->pushFrame(newState->prevPC, kf);
					newState->pc = kf->instructions; //(klee/include/klee/internal/Module/KInstruction.h)取出函数的入口地址
					if (statsTracker) //把返回地址压栈
						statsTracker->framePushed(*newState,
								&newState->stack[newState->stack.size()
										- 2]);

					unsigned numFormals = 1;
					for (unsigned i = 0; i < numFormals; ++i) {
						bindArgument(kf, i, *newState,
								arguments[i]); //这里才是实参与函数绑定（没有把实参压栈）
					}

					state.ptreeNode->data = 0;
					std::pair<PTree::Node*, PTree::Node*> res =
							processTree->split(state.ptreeNode,
									continueState, newState); //processTress在state.ptreeNode这个节点上split
					continueState->ptreeNode = res.first;
					newState->ptreeNode = res.second;

					std::swap(continueState, newState);

					///cc,return value
					return_value_handle(state, 0);
					return;
				}
				map_it++;
			}
			return_value_handle(state, -1);
		}
	} else {

		uint64_t val = 0;
		for (unsigned j = 0; j < numArgs; ++j) {

			ConstantExpr *CE = dyn_cast<ConstantExpr>(
					eval(ki, j + 1, state).value);

			if (j == 2) {
				val = CE->getZExtValue(); //把线程调用的函数名取出
			} else if (j == 3) {
				arguments.push_back(eval(ki, j + 1, state).value); //把调用函数时的参数取出
			}
		}
		//获得其线程标识符
		ref<Expr> idExpr = eval(ki, 1, state).value;
		//std::cout << "idExpr=" << idExpr << std::endl;
		ConstantExpr *CF = dyn_cast<ConstantExpr>(idExpr);
		int threadIdentify = CF->getZExtValue();
		//	std::cout << "threadAddr=" << threadIdentify << std::endl;

		uint64_t addr = 0;
		std::map<llvm::Function*, KFunction*>::const_iterator map_it =
				kmodule->functionMap.begin();

		while (map_it != kmodule->functionMap.end()) {
			addr = (uint64_t) map_it->first;
			if (val == addr) {

				ExecutionState *continueState, *newState;
				++stats::forks; //stats是state的链表，forks是state的个数
				continueState = &state;
				newState = state.branch();
				newState->pthreadId = ExecutionState::createPthreadId; //产生新的线程号，但不产生新的路径号
				ExecutionState::createPthreadId++;
				//wxf
				//--------此段代码用于检测可能数据竞争的位置----------
				if(checkDR)
				{
					printf("drc->CopyNodePointer %d %d \n",state.pthreadId,newState->pthreadId);
					drc->CopyNodePointer(state.pthreadId,newState->pthreadId);
				}

				//------------------------------------------------
				G_pthread_num++;//WXF 线程总数加1
				if(G_pthread_num >= pre_pthread_num){
					pre_pthread_num += 20;
					Thread_info_index = (Thread_info*)realloc(Thread_info_index,sizeof(Thread_info)*pre_pthread_num);
					memset(Thread_info_index+G_pthread_num*sizeof(Thread_info), 0, sizeof(Thread_info)*20);

					//addThreadNum();
					//--------此段代码用于检测可能数据竞争的位置----------
					if(checkDR)
						drc->AddThread();

					//------------------------------------------------
				}
				//wxf
				newState->isMain = 0; //非主线程
				newState->sumFunc = 1; //次线程的函数只调用了一层
				//hlm
				newState->snapShotList.clear();
				PthreadInfo *threadCon = new PthreadInfo(threadIdentify,
						newState->pthreadId);
				threadCon->isAlives.insert(
						pair<int, int>(newState->pathId, 1));
				threadList.push_back(threadCon);

				//hlm
				addedStates.insert(newState);

				delete newState->exeInfo;
				newState->exeInfo = new ExecutionInfo(); //创建线程的执行信息

				KFunction *kf = map_it->second; //取出f相对应函数

//				std::cout << newState << ","
//						<< kf->function->getName().data() << ","
//						<< newState->pthreadId << std::endl;

				newState->pushFrame(newState->prevPC, kf);
				newState->pc = kf->instructions; //(klee/include/klee/internal/Module/KInstruction.h)取出函数的入口地址
				if (statsTracker) //把返回地址压栈
					statsTracker->framePushed(*newState,
							&newState->stack[newState->stack.size()
									- 2]);

				unsigned numFormals = 1;
				for (unsigned i = 0; i < numFormals; ++i) {
					bindArgument(kf, i, *newState, arguments[i]); //这里才是实参与函数绑定（没有把实参压栈）
				}

				state.ptreeNode->data = 0;
				std::pair<PTree::Node*, PTree::Node*> res =
						processTree->split(state.ptreeNode,
								continueState, newState); //processTress在state.ptreeNode这个节点上split
				continueState->ptreeNode = res.first;
				newState->ptreeNode = res.second;

				std::swap(continueState, newState);

				///cc,return value
				return_value_handle(state, 0);
				return;
			}
			map_it++;
		}
		return_value_handle(state, -1);
	}
}

///cc,POSIX线程库函数仿真
//创建和销毁线程
//void Executor::call_pthread_create(ExecutionState &state, KInstruction* ki,
//		Instruction* i, unsigned numArgs, Value* fp, Function* f,
//		std::vector<ref<Expr> > &arguments)
//{
//	if (isMonitor)
//	{
//		int pathId = state.pathId;
//		//找到是那一条路径下的执行信息
//		struct ExecutionImage *ei = NULL;
//		for (std::set<ExecutionImage*>::iterator it =
//				executionImageList.begin(), ie = executionImageList.end();
//				it != ie; it++)
//		{
//			ei = *it;
//			if (ei->pathId == pathId)
//			{
//				break;
//			}
//		}
//		assert((ei != NULL) && ("路径拷贝监控信息出错！"));
//		if (ei->current == NULL)
//		{
//			return;
//		}
//
//		if ((ei->current != NULL) && (ei->current->type == 1)
//				&& (ei->current->threadId == state.pthreadId)) //当前指针是创建线程指针
//		{
//			//获取记录信息
//			int threadId;
//			threadId = ei->current->newPthreadId;
//			ei->current->exec = 1;
//
//			ExecutionState *st = NULL;
//
////			std::cout << "current->waitForExecutionStates.size="
////					<< ei->current->waitForExecutionStates.size() << std::endl;
//
//			for (std::vector<ExecutionState*>::iterator it =
//					ei->current->waitForExecutionStates.begin(), ie =
//					ei->current->waitForExecutionStates.end(); it != ie; it++)
//			{
//				st = *it;
//				assert((st != NULL) && "找不到等待的执行状态");
//
//				st->isWait = 0;
//				st->pc = st->prevPC;
////				std::cout << "线程:" << st->pthreadId << ",路径:" << st->pathId
////						<< ",st:" << st << "被唤醒\n";
//			}
//
//			ei->current->waitForExecutionStates.clear();
////			std::cout << "ei->current->waitForExecutionStates.size="
////					<< ei->current->waitForExecutionStates.size() << std::endl;
//
//			ei->current = ei->current->next;
//
//			uint64_t val = 0;
//			for (unsigned j = 0; j < numArgs; ++j)
//			{
//
//				ConstantExpr *CE = dyn_cast<ConstantExpr>(
//						eval(ki, j + 1, state).value);
//
//				if (j == 2)
//				{
//					val = CE->getZExtValue(); //把线程调用的函数名取出
//				}
//				else if (j == 3)
//				{
//					arguments.push_back(eval(ki, j + 1, state).value); //把调用函数时的参数取出
//				}
//			}
//
//			//获得其线程标识符
//			ref<Expr> idExpr = eval(ki, 1, state).value;
//			//std::cout << "idExpr=" << idExpr << std::endl;
//			ConstantExpr *CF = dyn_cast<ConstantExpr>(idExpr);
//			int threadIdentify = CF->getZExtValue();
//			//	std::cout << "threadAddr=" << threadIdentify << std::endl;
//
//			uint64_t addr = 0;
//			std::map<llvm::Function*, KFunction*>::const_iterator map_it =
//					kmodule->functionMap.begin();
//
//			while (map_it != kmodule->functionMap.end())
//			{
//				addr = (uint64_t) map_it->first;
//				if (val == addr)
//				{
//
//					ExecutionState *continueState, *newState;
//					++stats::forks; //stats是state的链表，forks是state的个数
//					continueState = &state;
//					newState = state.branch();
//					//newState->pthreadId = ExecutionState::createPthreadId; //产生新的线程号，但不产生新的路径号
//					//ExecutionState::createPthreadId++;
//
//					newState->pthreadId = threadId; //产生新的线程号，但不产生新的路径号
//
//					newState->isMain = 0; //非主线程
//					newState->sumFunc = 1; //次线程的函数只调用了一层
//					//hlm
//					newState->snapShotList.clear();
//					PthreadInfo *threadCon = new PthreadInfo(threadIdentify,
//							newState->pthreadId);
//					threadCon->isAlives.insert(
//							pair<int, int>(newState->pathId, 1));
//					threadList.push_back(threadCon);
//
//					//hlm
//					addedStates.insert(newState);
//
//					delete newState->exeInfo;
//					newState->exeInfo = new ExecutionInfo(); //创建线程的执行信息
//
//					KFunction *kf = map_it->second; //取出f相对应函数
//
//					newState->pushFrame(newState->prevPC, kf);
//					newState->pc = kf->instructions; //(klee/include/klee/internal/Module/KInstruction.h)取出函数的入口地址
//					if (statsTracker) //把返回地址压栈
//						statsTracker->framePushed(*newState,
//								&newState->stack[newState->stack.size() - 2]);
//
//					unsigned numFormals = 1;
//					for (unsigned i = 0; i < numFormals; ++i)
//					{
//						bindArgument(kf, i, *newState, arguments[i]); //这里才是实参与函数绑定（没有把实参压栈）
//					}
//
//					state.ptreeNode->data = 0;
//					std::pair<PTree::Node*, PTree::Node*> res =
//							processTree->split(state.ptreeNode, continueState,
//									newState); //processTress在state.ptreeNode这个节点上split
//					continueState->ptreeNode = res.first;
//					newState->ptreeNode = res.second;
//
//					std::swap(continueState, newState);
//
//					///cc,return value
//					return_value_handle(state, 0);
//					return;
//				}
//				map_it++;
//			}
//			return_value_handle(state, -1);
//		}
//		else //当前指针不是创建线程指针
//		{
//			if (ei->current == NULL)
//			{
////				printf("当前指针为NULL\n");
//				return;
//			}
//			else
//			{
////				std::cout << "state的路径号为:" << state.pathId << ",线程号为:"
////						<< state.pthreadId << std::endl;
////				std::cout << "current的路径号为:" << ei->pathId << ",线程号为:"
////						<< ei->current->threadId << std::endl;
////				std::cout << "等待创建线程\n";
//
//				struct exePthreadInfo *p;
//				if (ei->current->disableFlag == 1) //当前current指针已经指示处于等待的线程，所以本state可以不等待这个执行结束，否则容易产生死锁
//				{
//					p = ei->current;
//					while (p->disableFlag == 1)
//						p = p->next;
//					if (p->threadId != state.pthreadId) //可以執行的线程不是本线程，则等待该线程执行结束
//					{
//						state.isWait = 1;
//						p->waitForExecutionStates.push_back(&state);
////						std::cout << "线程:" << state.pthreadId << ",路径:"
////								<< state.pathId << ",state:" << &state
////								<< "进入等待状态\n";
//					}
//					else
//					{
//						state.pc = state.prevPC;
//					}
//
//				}
//				else
//				{
//					state.isWait = 1;
//					ei->current->waitForExecutionStates.push_back(&state);
////					std::cout << "线程:" << state.pthreadId << ",路径:"
////							<< state.pathId << ",state:" << &state
////							<< "进入等待状态\n";
//				}
//			}
//		}
//	}
//	else
//	{
//		uint64_t val = 0;
//		for (unsigned j = 0; j < numArgs; ++j)
//		{
//
//			ConstantExpr *CE = dyn_cast<ConstantExpr>(
//					eval(ki, j + 1, state).value);
//
//			if (j == 2)
//			{
//				val = CE->getZExtValue(); //把线程调用的函数名取出
//			}
//			else if (j == 3)
//			{
//				arguments.push_back(eval(ki, j + 1, state).value); //把调用函数时的参数取出
//			}
//		}
//
//		//获得其线程标识符
//		ref<Expr> idExpr = eval(ki, 1, state).value;
//		//std::cout << "idExpr=" << idExpr << std::endl;
//		ConstantExpr *CF = dyn_cast<ConstantExpr>(idExpr);
//		int threadIdentify = CF->getZExtValue();
//		//	std::cout << "threadAddr=" << threadIdentify << std::endl;
//
//		uint64_t addr = 0;
//		std::map<llvm::Function*, KFunction*>::const_iterator map_it =
//				kmodule->functionMap.begin();
//
//		while (map_it != kmodule->functionMap.end())
//		{
//			addr = (uint64_t) map_it->first;
//			if (val == addr)
//			{
//
//				ExecutionState *continueState, *newState;
//				++stats::forks; //stats是state的链表，forks是state的个数
//				continueState = &state;
//				newState = state.branch();
//				newState->pthreadId = ExecutionState::createPthreadId; //产生新的线程号，但不产生新的路径号
//				ExecutionState::createPthreadId++;
//
//				newState->isMain = 0; //非主线程
//				newState->sumFunc = 1; //次线程的函数只调用了一层
//				//hlm
//				newState->snapShotList.clear();
//				PthreadInfo *threadCon = new PthreadInfo(threadIdentify,
//						newState->pthreadId);
//				threadCon->isAlives.insert(pair<int, int>(newState->pathId, 1));
//				threadList.push_back(threadCon);
//
//				//hlm
//				addedStates.insert(newState);
//
//				delete newState->exeInfo;
//				newState->exeInfo = new ExecutionInfo(); //创建线程的执行信息
//
//				KFunction *kf = map_it->second; //取出f相对应函数
//
//				newState->pushFrame(newState->prevPC, kf);
//				newState->pc = kf->instructions; //(klee/include/klee/internal/Module/KInstruction.h)取出函数的入口地址
//				if (statsTracker) //把返回地址压栈
//					statsTracker->framePushed(*newState,
//							&newState->stack[newState->stack.size() - 2]);
//
//				unsigned numFormals = 1;
//				for (unsigned i = 0; i < numFormals; ++i)
//				{
//					bindArgument(kf, i, *newState, arguments[i]); //这里才是实参与函数绑定（没有把实参压栈）
//				}
//
//				state.ptreeNode->data = 0;
//				std::pair<PTree::Node*, PTree::Node*> res = processTree->split(
//						state.ptreeNode, continueState, newState); //processTress在state.ptreeNode这个节点上split
//				continueState->ptreeNode = res.first;
//				newState->ptreeNode = res.second;
//
//				std::swap(continueState, newState);
//
//				///cc,return value
//				return_value_handle(state, 0);
//				return;
//			}
//			map_it++;
//		}
//		return_value_handle(state, -1);
//	}
//}

void Executor::call_pthread_exit(ExecutionState &state, KInstruction* ki,
		Instruction* i, unsigned numArgs, Value* fp, Function* f,
		std::vector<ref<Expr> > &arguments) {
//		std::cout << "进去pthread_exit\n";
	ref<Expr> para = eval(ki, 1, state).value;

	int threadID = state.pthreadId;
	int pathID = state.pathId;
	PthreadInfo *pthread = NULL;
	for (std::vector<PthreadInfo*>::iterator itp = threadList.begin(), iep =
			threadList.end(); itp != iep; itp++) {
		pthread = *itp;
		if (pthread->threadId == threadID) {
			break;
		}
	}
	assert((pthread != NULL) && "线程不存在");

	ExecutionState *st = NULL;

	for (std::vector<ExecutionState*>::iterator it =
			pthread->waitExitStates.begin(), ie =
			pthread->waitExitStates.end(); it != ie; it++) {
		if (pthread->waitExitStates.size() != 0) {

			st = *it;
			assert((st != NULL) && "找不到等待的执行状态");
			assert(st->prevPC->inst != NULL);
			if (st->pathId == pathID) {

				CallSite css(st->prevPC->inst);
				Value *ffp = css.getCalledValue();
				Function *ff = getTargetFunction(ffp, state);
				assert(ff != NULL);
				KFunction *kff = new KFunction(ff, kmodule);
				assert(kff != NULL);
				KInstruction *kii = st->prevPC;
				ref<Expr> fpara = eval(kii, 2, *st).value;

				ConstantExpr *CE = dyn_cast<ConstantExpr>(fpara);
				uint64_t val = 0;
				if (CE != 0) {
					val = CE->getZExtValue();
					if (val != 0) {
						executeMemoryOperation(*st, true, fpara,
								para, kii);
					}
				}
				st->isWait = 0;

				pthread->waitExitStates.erase(it);
			}
		}
	}

	map<int, int>::iterator it1;
	it1 = pthread->isAlives.find(state.pathId);
	if (it1 != pthread->isAlives.end()) {
		it1->second = 0;
	}

	pthread->retExprs.insert(std::make_pair(state.pathId, para));

	this->terminateStateOnExit(state);
//	std::cout << "线程" << state.pthreadId << "路径" << state.pathId << "执行结束\n";

}

void Executor::call_pthread_detach(ExecutionState &state, KInstruction* ki,
		Instruction* i, unsigned numArgs, Value* fp, Function* f,
		std::vector<ref<Expr> > &arguments) {

}

void Executor::call_pthread_join(ExecutionState &state, KInstruction* ki,
		Instruction* i, unsigned numArgs, Value* fp, Function* f,
		std::vector<ref<Expr> > &arguments) {

//	std::cout << "线程" << state.pthreadId << ",pathId=" << state.pathId
//			<< "进入pthread_join\n";

	assert(!state.loadExpr.isNull());
	ConstantExpr *CE = dyn_cast<ConstantExpr>(state.loadExpr);
	int threadIdentify = CE->getZExtValue();
//	std::cout << "threadIdentify=" << threadIdentify << std::endl;

	PthreadInfo *pthread = NULL;
	for (std::vector<PthreadInfo*>::iterator itp = threadList.begin(), iep =
			threadList.end(); itp != iep; itp++) {
		pthread = *itp;
		if (pthread->threadIdentify == threadIdentify) {
			break;
		}
	}

	assert((pthread != NULL) && "线程不存在");

	std::map<int, int>::iterator it1;
	it1 = pthread->isAlives.find(state.pathId);
	if (it1 != pthread->isAlives.end()) {
		if (it1->second == 1) {
//			std::cout << "状态没有结束\n";
			state.isWait = 1;
			pthread->waitExitStates.push_back(&state);
		} else {
//			std::cout << "状态已经结束\n";
			std::map<int, ref<Expr> >::iterator it2;
			it2 = pthread->retExprs.find(state.pathId);
			ref<Expr> val = it2->second;
			ref<Expr> addr = eval(ki, 2, state).value;
			ConstantExpr * CE = dyn_cast<ConstantExpr>(addr);
			uint64_t tt = 0;
			if (CE != 0) {
				tt = CE->getZExtValue();
				if ((tt != 0) && (!val.isNull())) {
					executeMemoryOperation(state, true, addr, val,
							ki);
				}
			}
		}
	}

}

void Executor::call_pthread_cancel(ExecutionState &state, KInstruction* ki,
		Instruction* i, unsigned numArgs, Value* fp, Function* f,
		std::vector<ref<Expr> > &arguments) {
	assert(!state.loadExpr.isNull());
	ConstantExpr *CE = dyn_cast<ConstantExpr>(state.loadExpr);
	int threadIdentify = CE->getZExtValue();
//	std::cout << "threadIdentify=" << threadIdentify << std::endl;

	PthreadInfo *pthread = NULL;
	for (std::vector<PthreadInfo*>::iterator itp = threadList.begin(), iep =
			threadList.end(); itp != iep; itp++) {
		pthread = *itp;
		if (pthread->threadIdentify == threadIdentify) {
			break;
		}
	}

	for (std::set<ExecutionState*>::iterator it = states.begin(), ie =
			states.end(); it != ie; it++) {
		ExecutionState *st = *it;
		if (st->pthreadId == pthread->threadId) {
			this->terminateStateOnExit(*st);
			std::map<int, int>::iterator l_it;
			l_it = pthread->isAlives.find(st->pathId);
			if (l_it != pthread->isAlives.end()) {
				l_it->second = 0;
			}
		}
	}

}

//创建和销毁互斥量
void Executor::call_pthread_mutex_init(ExecutionState &state, KInstruction* ki,
		Instruction* i, unsigned numArgs, Value* fp, Function* f,
		std::vector<ref<Expr> > &arguments) {

	ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
	uint64_t val = 0;
	if (CE != 0) {
		val = CE->getZExtValue();
		MutexInfo *mutex = new MutexInfo(val, 0, NULL);
		mutexinfolist.push_back(mutex);
	}

}

void Executor::call_pthread_mutex_destroy(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {

	unsigned int aa = 0;
	ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);

	MutexInfo *mutex = NULL;
	uint64_t val = 0;
	if (CE != 0) {
		val = CE->getZExtValue();
		for (aa = 0; aa < this->mutexinfolist.size(); aa++) {
			int mutexID = mutexinfolist[aa]->getMutex();
			if (mutexID == val) {
				mutex = mutexinfolist[aa];
				break;
			}
		}

	}

	assert((mutex != NULL) && "互斥量没有初始化!");
	mutexinfolist.erase(mutexinfolist.begin() + aa);

}

void Executor::call_pthread_mutex_lock(ExecutionState &state, KInstruction* ki,
		Instruction* i, unsigned numArgs, Value* fp, Function* f,
		std::vector<ref<Expr> > &arguments) {
	unsigned int aa = 0;
	if (isMonitor) {
		int pathId = state.pathId;

		//找到是那一条路径下的执行信息
		struct ExecutionImage *ei = NULL;
		for (std::set<ExecutionImage*>::iterator it =
				executionImageList.begin(), ie =
				executionImageList.end(); it != ie; it++) {
			ei = *it;
			if (ei->pathId == pathId) {
				break;
			}
		}
		assert((ei!=NULL)&&("路径拷贝监控信息出错！"));

		struct exePthreadInfo *p = ei->head;
		while (p) {
			if ((p->threadId == state.pthreadId) && (p->lockOrder > 0)
					&& (p->exec == 0) && (p->type == 2)) {
				state.currentLockOrder = p->lockOrder;
				state.appMutexAddr = p->mutexAddr;
				break;
			}
			p = p->next;
		}

//		printf("state.pthreadId=%d\n", state.pthreadId);
//		printf("state.currentLockOrder = %d\n", state.currentLockOrder);
//		printf("exeLockOrder = %d\n", exeLockOrder);

		if (state.currentLockOrder != exeLockOrder) {
			state.isWait = 1;
			return;
		}

		if (p) {
			p->exec = 1;
		}

//		printf("BBB\n");
		exeLockOrder++;
		state.currentLockOrder = 0;
		state.appMutexAddr = 0;

		ref<Expr> base = eval(ki, 1, state).value;
		ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
		uint64_t val = 0;
		BasicBlock *parent = i->getParent();
		Function *ff = parent->getParent();
		int flag = 0;

		if (CE != 0) {
			val = CE->getZExtValue();
			///cc,lock operate
			state.processInfo->callMutexLock(state, val);

			MutexInfo *mutex = NULL;
			for (aa = 0; aa < this->mutexinfolist.size(); aa++) {
				int tmpmutex = mutexinfolist[aa]->getMutex();
				if (tmpmutex == val) {
					mutex = mutexinfolist[aa];
					flag = 1;
					break;
				}
			}
			if (flag == 0) {
				mutex = new MutexInfo(val, 0, NULL);
				mutexinfolist.push_back(mutex);
			}

		}
	} else {
		ref<Expr> base = eval(ki, 1, state).value;
		ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
		uint64_t val = 0;
		BasicBlock *parent = i->getParent();
		Function *ff = parent->getParent();
		int flag = 0;

		if (CE != 0) {
			val = CE->getZExtValue();
			///cc,lock operate
			state.processInfo->callMutexLock(state, val);

			MutexInfo *mutex = NULL;
			for (aa = 0; aa < this->mutexinfolist.size(); aa++) {
				int tmpmutex = mutexinfolist[aa]->getMutex();
				if (tmpmutex == val) {
					mutex = mutexinfolist[aa];
					flag = 1;
					break;
				}
			}
			if (flag == 0) {
				mutex = new MutexInfo(val, 0, NULL);
				mutexinfolist.push_back(mutex);
			}

			state.ownMutexList.push_back(val);
			//拷贝状态
			ExecutionState *st = new ExecutionState(state);

			st->pc = st->prevPC;

			ExecutionSnapShot *snapshot = new ExecutionSnapShot(
					state.pthreadId, state.pathId,
					state.ptreeNode->nodeId, val, st);
			state.snapShotList.push_back(snapshot);
		}
		//		std::cout << "线程:" << state.pthreadId << ",路径:" << state.pathId
		//				<< ",state:" << &state << ",lock操作结束\n";
	}
}

//加锁互斥量
//void Executor::call_pthread_mutex_lock(ExecutionState &state, KInstruction* ki,
//		Instruction* i, unsigned numArgs, Value* fp, Function* f,
//		std::vector<ref<Expr> > &arguments)
//{
//
//	unsigned int aa = 0;
//
//	if (isMonitor)
//	{
//
//		int pathId = state.pathId;
//
////找到是那一条路径下的执行信息
//		struct ExecutionImage *ei = NULL;
//		for (std::set<ExecutionImage*>::iterator it =
//				executionImageList.begin(), ie = executionImageList.end();
//				it != ie; it++)
//		{
//			ei = *it;
//			if (ei->pathId == pathId)
//			{
//				break;
//			}
//		}
//		assert((ei!=NULL)&&("路径拷贝监控信息出错！"));
//
//		if ((ei->current == NULL) && (ei->pre == NULL))
//		{
//			return;
//		}
//
//		if (ei->current != NULL)
//		{
////			printf("current->disableFlag=%d,current->pathId=%d\n",
////					ei->current->disableFlag, ei->pathId);
//		}
//		if ((ei->current != NULL) && (ei->current->disableFlag == 1)
//				&& (ei->pre == NULL))
//		{
//			state.pc = state.prevPC;
//			while ((ei->current != NULL)
//					&& ((ei->current->disableFlag == 1)
//							|| (ei->current->exec == 1)))
//			{
//				ei->current = ei->current->next;
//			}
//			return;
//		}
//
//		if (ei->pre != NULL) //pre!=NULL;
//		{
//			if (ei->pre->type == 2)
//			{
//				if (ei->pre->threadId == state.pthreadId) //同一个线程
//				{
//					ei->pre->exec = 1;
//					ExecutionState *st = NULL;
//
////					std::cout << "pre->waitForExecutionStates.size="
////							<< ei->pre->waitForExecutionStates.size()
////							<< std::endl;
//
//					for (std::vector<ExecutionState*>::iterator it =
//							ei->pre->waitForExecutionStates.begin(), ie =
//							ei->pre->waitForExecutionStates.end(); it != ie;
//							it++)
//					{
//						st = *it;
//						assert((st!=NULL)&&"找不到等待的执行状态");
//
//						st->isWait = 0;
//						st->pc = st->prevPC;
////						std::cout << "线程:" << st->pthreadId << ",路径:"
////								<< st->pathId << ",st:" << st << "被唤醒\n";
//
//					}
//
//					ei->pre->waitForExecutionStates.clear();
////					std::cout << "pre->waitForExecutionStates.size="
////							<< ei->pre->waitForExecutionStates.size()
////							<< std::endl;
//					if (ei->current == ei->pre)
//					{
//						ei->current = ei->current->next;
//					}
//					ei->pre = NULL;
//
//					ref<Expr> base = eval(ki, 1, state).value;
//					ConstantExpr *CE = dyn_cast<ConstantExpr>(
//							eval(ki, 1, state).value);
//					uint64_t val = 0;
//					BasicBlock *parent = i->getParent();
//					Function *ff = parent->getParent();
//					int flag = 0;
//
//					if (CE != 0)
//					{
//						val = CE->getZExtValue();
//						///cc,lock operate
//						state.processInfo->callMutexLock(state, val);
//
//						MutexInfo *mutex = NULL;
//						for (aa = 0; aa < this->mutexinfolist.size(); aa++)
//						{
//							int tmpmutex = mutexinfolist[aa]->getMutex();
//							if (tmpmutex == val)
//							{
//								mutex = mutexinfolist[aa];
//								flag = 1;
//								break;
//							}
//						}
//						if (flag == 0)
//						{
//							mutex = new MutexInfo(val, 0, NULL);
//							mutexinfolist.push_back(mutex);
//						}
//						//hlm
//						//拷贝状态
//						ExecutionState *st = new ExecutionState(state);
//
//						st->pc = st->prevPC;
//
//						ExecutionSnapShot *snapshot = new ExecutionSnapShot(
//								state.pthreadId, state.pathId,
//								state.ptreeNode->nodeId, val, st);
//						state.snapShotList.push_back(snapshot);
//
//					}
//
////					std::cout << "线程:" << state.pthreadId << ",路径:"
////							<< state.pathId << ",state:" << &state
////							<< ",lock操作结束\n";
//
//				}
//				else //当前执行线程不是pre所指向的线程
//				{
//
////					std::cout << "state的线程号为:" << state.pthreadId << ",路径为:"
////							<< state.pathId << std::endl;
////					std::cout << "pre的线程号为:" << ei->pre->threadId << ",路径为:"
////							<< ei->pathId << std::endl;
//
//					struct exePthreadInfo *p;
//					if (ei->pre->disableFlag == 1) //当前current指针已经指示处于等待的线程，所以本state可以不等待这个执行结束，否则容易产生死锁
//					{
//						p = ei->pre;
//						while (p->disableFlag == 1)
//							p = p->next;
//						if (p->threadId != state.pthreadId) //可以執行的线程不是本线程，则等待该线程执行结束
//						{
//							state.isWait = 1;
//							p->waitForExecutionStates.push_back(&state);
////							std::cout << "线程:" << state.pthreadId << ",路径:"
////									<< state.pathId << ",state:" << &state
////									<< "进入等待状态\n";
//						}
//						else
//						{
//							state.pc = state.prevPC;
//						}
//
//					}
//					else
//					{
//						state.isWait = 1;
//						ei->pre->waitForExecutionStates.push_back(&state);
////						std::cout << "线程:" << state.pthreadId << ",路径:"
////								<< state.pathId << ",state:" << &state
////								<< "进入等待状态\n";
//					}
//				}
//			}
//			else //pre->type!=2;
//			{
////				std::cout << "state的线程号为:" << state.pthreadId << ",路径号为:"
////						<< state.pathId << std::endl;
////				std::cout << "pre的线程号为:" << ei->pre->threadId << ",路径号为:"
////						<< ei->pathId << ",操作类型为:" << ei->pre->type
////						<< std::endl;
//
//				struct exePthreadInfo *p;
//				if (ei->pre->disableFlag == 1) //当前current指针已经指示处于等待的线程，所以本state可以不等待这个执行结束，否则容易产生死锁
//				{
//					p = ei->pre;
//					while (p->disableFlag == 1)
//						p = p->next;
//					if (p->threadId != state.pthreadId) //可以執行的线程不是本线程，则等待该线程执行结束
//					{
//						state.isWait = 1;
//						p->waitForExecutionStates.push_back(&state);
////						std::cout << "线程:" << state.pthreadId << ",路径:"
////								<< state.pathId << ",state:" << &state
////								<< "进入等待状态\n";
//					}
//					else
//					{
//						state.pc = state.prevPC;
//					}
//
//				}
//				else
//				{
//					state.isWait = 1;
//					ei->pre->waitForExecutionStates.push_back(&state);
////					std::cout << "线程:" << state.pthreadId << ",路径:"
////							<< state.pathId << ",state:" << &state
////							<< "进入等待状态\n";
//				}
//			}
//		}
//		else //pre=NULL;则current有效
//		{
//
//			if ((ei->current != NULL) && (ei->current->type == 2))
//			{
//				if (ei->current->threadId == state.pthreadId)
//				{
//					ei->current->exec = 1;
//					ExecutionState *st = NULL;
////					std::cout << "current->waitForExecutionStates.size="
////							<< ei->current->waitForExecutionStates.size()
////							<< std::endl;
//					for (std::vector<ExecutionState*>::iterator it =
//							ei->current->waitForExecutionStates.begin(), ie =
//							ei->current->waitForExecutionStates.end(); it != ie;
//							it++)
//					{
//
//						st = *it;
//						assert((st!=NULL)&&"找不到等待的执行状态");
//
//						st->isWait = 0;
//						st->pc = st->prevPC;
////						std::cout << "线程:" << st->pthreadId << ",路径:"
////								<< st->pathId << ",st:" << st << "被唤醒\n";
//					}
//
//					ei->current->waitForExecutionStates.clear();
//
////					std::cout << "current->waitForExecutionStates.size="
////							<< ei->current->waitForExecutionStates.size()
////							<< std::endl;
//
//					ei->current = ei->current->next;
//
//					ref<Expr> base = eval(ki, 1, state).value;
//					ConstantExpr *CE = dyn_cast<ConstantExpr>(
//							eval(ki, 1, state).value);
//					uint64_t val = 0;
//					BasicBlock *parent = i->getParent();
//					Function *ff = parent->getParent();
//					int flag = 0;
//
//					if (CE != 0)
//					{
//						val = CE->getZExtValue();
//
//						///cc,lock operate
//						state.processInfo->callMutexLock(state, val);
//						MutexInfo *mutex = NULL;
//						for (aa = 0; aa < this->mutexinfolist.size(); aa++)
//						{
//							int tmpmutex = mutexinfolist[aa]->getMutex();
//							if (tmpmutex == val)
//							{
//								mutex = mutexinfolist[aa];
//								flag = 1;
//								break;
//							}
//						}
//						if (flag == 0)
//						{
//							mutex = new MutexInfo(val, 0, NULL);
//							mutexinfolist.push_back(mutex);
//						}
//						//hlm
//						//拷贝状态
//						ExecutionState *st = new ExecutionState(state);
//						st->pc = st->prevPC;
//						ExecutionSnapShot *snapshot = new ExecutionSnapShot(
//								state.pthreadId, state.pathId,
//								state.ptreeNode->nodeId, val, st);
//						state.snapShotList.push_back(snapshot);
//					}
//
////					std::cout << "线程:" << state.pthreadId << ",路径:"
////							<< state.pathId << ",state:" << &state
////							<< ",lock操作结束\n";
//
//				}
//				else
//				{
////					std::cout << "state的线程号为:" << state.pthreadId << ",路径号为:"
////							<< state.pathId << std::endl;
////					std::cout << "current的线程号为:" << ei->current->threadId
////							<< ",路径号为:" << ei->pathId << std::endl;
//
//					struct exePthreadInfo *p;
//					if (ei->current->disableFlag == 1) //当前current指针已经指示处于等待的线程，所以本state可以不等待这个执行结束，否则容易产生死锁
//					{
//						p = ei->current;
//						while (p->disableFlag == 1)
//							p = p->next;
//						if (p->threadId != state.pthreadId) //可以執行的线程不是本线程，则等待该线程执行结束
//						{
//							state.isWait = 1;
//							p->waitForExecutionStates.push_back(&state);
////							std::cout << "线程:" << state.pthreadId << ",路径:"
////									<< state.pathId << ",state:" << &state
////									<< "进入等待状态\n";
//						}
//						else
//						{
//							state.pc = state.prevPC;
//						}
//
//					}
//					else
//					{
//						state.isWait = 1;
//						ei->current->waitForExecutionStates.push_back(&state);
////						std::cout << "线程:" << state.pthreadId << ",路径:"
////								<< state.pathId << ",state:" << &state
////								<< "进入等待状态\n";
//					}
//				}
//			}
//			else
//			{
//				if (ei->current == NULL)
//				{
////					printf("当前指针为NULL\n");
//					return;
//				}
//				else
//				{
////					std::cout << "state的线程号为:" << state.pthreadId << ",路径号为:"
////							<< state.pathId << std::endl;
////					std::cout << "current的线程号为:" << ei->current->threadId
////							<< ",路径号为:" << ei->pathId << ",操作类型为:"
////							<< ei->current->type << std::endl;
//
//					struct exePthreadInfo *p;
//					if (ei->current->disableFlag == 1) //当前current指针已经指示处于等待的线程，所以本state可以不等待这个执行结束，否则容易产生死锁
//					{
//						p = ei->current;
//						while (p->disableFlag == 1)
//							p = p->next;
//						if (p->threadId != state.pthreadId) //可以執行的线程不是本线程，则等待该线程执行结束
//						{
//							state.isWait = 1;
//							p->waitForExecutionStates.push_back(&state);
////							std::cout << "线程:" << state.pthreadId << ",路径:"
////									<< state.pathId << ",state:" << &state
////									<< "进入等待状态\n";
//						}
//						else
//						{
//							state.pc = state.prevPC;
//						}
//
//					}
//					else
//					{
//						state.isWait = 1;
//						ei->current->waitForExecutionStates.push_back(&state);
////						std::cout << "线程:" << state.pthreadId << ",路径:"
////								<< state.pathId << ",state:" << &state
////								<< "进入等待状态\n";
//					}
//				}
//			}
//		}
//	}
//	else
//	{
//
//		ref<Expr> base = eval(ki, 1, state).value;
//		ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
//		uint64_t val = 0;
//		BasicBlock *parent = i->getParent();
//		Function *ff = parent->getParent();
//		int flag = 0;
//
//		if (CE != 0)
//		{
//			val = CE->getZExtValue();
//			///cc,lock operate
//			state.processInfo->callMutexLock(state, val);
//
//			MutexInfo *mutex = NULL;
//			for (aa = 0; aa < this->mutexinfolist.size(); aa++)
//			{
//				int tmpmutex = mutexinfolist[aa]->getMutex();
//				if (tmpmutex == val)
//				{
//					mutex = mutexinfolist[aa];
//					flag = 1;
//					break;
//				}
//			}
//			if (flag == 0)
//			{
//				mutex = new MutexInfo(val, 0, NULL);
//				mutexinfolist.push_back(mutex);
//			}
//
//			state.ownMutexList.push_back(val);
//			//拷贝状态
//			ExecutionState *st = new ExecutionState(state);
//
//			st->pc = st->prevPC;
//
//			ExecutionSnapShot *snapshot = new ExecutionSnapShot(state.pthreadId,
//					state.pathId, state.ptreeNode->nodeId, val, st);
//			state.snapShotList.push_back(snapshot);
//		}
////		std::cout << "线程:" << state.pthreadId << ",路径:" << state.pathId
////				<< ",state:" << &state << ",lock操作结束\n";
//	}
//}

//尝试加锁互斥量
void Executor::call_pthread_mutex_trylock(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {
	ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
	uint64_t val = 0;
	if (CE != 0) {
		val = CE->getZExtValue();
		///cc,lock operate
		if (state.processInfo->callMutexTryLock(state, val)) {
			return_value_handle(state, 0);
		} else {
			return_value_handle(state, -1);
		}
	}
}

void Executor::call_pthread_mutex_unlock(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {
	unsigned int aa = 0;
	if (isMonitor) {
		int pathId = state.pathId;

		//找到是那一条路径下的执行信息
		struct ExecutionImage *ei = NULL;
		for (std::set<ExecutionImage*>::iterator it =
				executionImageList.begin(), ie =
				executionImageList.end(); it != ie; it++) {
			ei = *it;
			if (ei->pathId == pathId) {
				break;
			}
		}
		assert((ei != NULL) && ("路径拷贝监控信息出错！"));

		ExecutionState *st = NULL;

//		printf("In The pthread_mutex_unlock\n");
//
//		printf("states.size= %d\n", states.size());

		std::set<ExecutionState*>::iterator it = states.begin();
		std::set<ExecutionState*>::iterator ie = states.end();
//		printf("+++++++++++++++++++++++++++++++++\n");
		for (; it != ie; it++) {
			st = *it;

//			printf("st->pthreadId=%d\n", st->pthreadId);
//			printf("st->currentLockOrder = %d\n", st->currentLockOrder);
//			printf("exeLockOrder = %d\n", exeLockOrder);

			if (st->currentLockOrder == exeLockOrder) {
//				printf("st>iswait = %d\n", st->isWait);

				if (st->isWait == 1) {
//					printf("st->pthreadId=%d被唤醒\n", st->pthreadId);
//					printf("st->currentLockOrder = %d\n", st->currentLockOrder);
//					printf("exeLockOrder = %d\n", exeLockOrder);
					st->pc = st->prevPC;
					st->isWait = 0;
				}

			}
		}
//		printf("+++++++++++++++++++++++++++++++++\n");

//		printf("CCC\n");

		ref<Expr> base = eval(ki, 1, state).value;
		ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
		uint64_t val = 0;
		BasicBlock *parent = i->getParent();
		Function *ff = parent->getParent();

		if (CE != 0) {
			val = CE->getZExtValue();
			//cc
			state.processInfo->callMutexUnlock(state, val);
			//cc
			MutexInfo *mutex = NULL;
			for (aa = 0; aa < this->mutexinfolist.size(); aa++) {
				int tmpmutex = mutexinfolist[aa]->getMutex();
				if (tmpmutex == val) {
					mutex = mutexinfolist[aa];
					break;
				}
			}
			//hlm

			ExecutionSnapShot *snapshot = NULL;

			for (unsigned int aa = 0; aa < state.snapShotList.size();
					aa++) {
				snapshot = state.snapShotList[aa];
				if (snapshot->mutex == val) {
					//						state.snapShotList.erase(
					//								state.snapShotList.begin() + aa);
					break;
				}
			}
		}
	} else {
		ref<Expr> base = eval(ki, 1, state).value;
		ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
		uint64_t val = 0;
		BasicBlock *parent = i->getParent();
		Function *ff = parent->getParent();

		if (CE != 0) {
			val = CE->getZExtValue();
			//cc
			state.processInfo->callMutexUnlock(state, val);
			//PC
			MutexInfo *mutex = NULL;
			for (aa = 0; aa < this->mutexinfolist.size(); aa++) {
				int tmpmutex = mutexinfolist[aa]->getMutex();
				if (tmpmutex == val) {
					mutex = mutexinfolist[aa];
					break;
				}
			}
			//hlm

			for (aa = 0; aa < state.ownMutexList.size(); aa++) {
				int tmpMu = state.ownMutexList[aa];
				if (tmpMu == val) {
					break;
				}
			}

			state.ownMutexList.erase(state.ownMutexList.begin() + aa);

			ExecutionSnapShot *snapshot = NULL;

			for (aa = 0; aa < state.snapShotList.size(); aa++) {
				snapshot = state.snapShotList[aa];
				if (snapshot->mutex == val) {
					//						state.snapShotList.erase(
					//								state.snapShotList.begin() + aa);
					break;
				}
			}
		}
		//		std::cout << "线程：" << state.pthreadId << ",路径：" << state.pathId
		//				<< ",state:" << &state << ",进行unlock操作结束\n";
	}
}

//解锁互斥量
//void Executor::call_pthread_mutex_unlock(ExecutionState &state,
//		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
//		Function* f, std::vector<ref<Expr> > &arguments)
//{
//	unsigned int aa = 0;
//	if (isMonitor)
//	{
//		int pathId = state.pathId;
//
////找到是那一条路径下的执行信息
//		struct ExecutionImage *ei = NULL;
//		for (std::set<ExecutionImage*>::iterator it =
//				executionImageList.begin(), ie = executionImageList.end();
//				it != ie; it++)
//		{
//			ei = *it;
//			if (ei->pathId == pathId)
//			{
//				break;
//			}
//		}
//		assert((ei != NULL) && ("路径拷贝监控信息出错！"));
//		if (ei->current == NULL)
//		{
//			return;
//		}
//
//		if ((ei->current != NULL) && (ei->current->type == 3))
//		{
//			if (ei->current->threadId == state.pthreadId)
//			{
//				ei->current->exec = 1;
//				ExecutionState *st = NULL;
////				std::cout << "current->waitForExecutionStates.size="
////						<< ei->current->waitForExecutionStates.size()
////						<< std::endl;
//				for (std::vector<ExecutionState*>::iterator it =
//						ei->current->waitForExecutionStates.begin(), ie =
//						ei->current->waitForExecutionStates.end(); it != ie;
//						it++)
//				{
//					st = *it;
//					assert((st != NULL) && "找不到等待的执行状态");
//
//					st->isWait = 0;
//					st->pc = st->prevPC;
////					std::cout << "线程:" << st->pthreadId << ",路径:" << st->pathId
////							<< ",st:" << st << "被唤醒\n";
//				}
//
//				ei->current->waitForExecutionStates.clear();
////				std::cout << "current->waitForExecutionStates.size="
////						<< ei->current->waitForExecutionStates.size()
////						<< std::endl;
////
////				unsigned long mutexAddr = ei->current->mutexAddr;
////
////				struct exePthreadInfo *p = ei->head;
////				struct exePthreadInfo *q = NULL;
////				int td = -1;
////
////				q = ei->current->next;
////				while (q != NULL) //如果存在多个等待lock情形，看哪一个先对其unlock的
////				{
////					if ((q->type == 3) && (q->threadId != state.pthreadId)
////							&& (q->mutexAddr == mutexAddr))
////					{
////						td = q->threadId;
////						break;
////					}
////					q = q->next;
////				}
////
////				if (q != NULL) //找到那个先对其unlock的进行指向pre，记录中有unlock情况
////				{
////					struct exePthreadInfo *r = ei->head;
////					while ((r != NULL) && (r < ei->current))
////					{
////						if ((r->type == 2) && (r->disableFlag == 1)
////								&& (r->threadId == td) && (r->exec == 0)
////								&& (r->mutexAddr == q->mutexAddr))
////						{
////							r->disableFlag = 0;
////							ei->pre = r;
////							r = NULL;
////							break;
////						}
////						r = r->next;
////					}
////				}
////				else //记录中没有unlock情况
////				{
////					struct exePthreadInfo *r = ei->head;
////					while ((r != NULL) && (r < ei->current))
////					{
////						if ((r->type == 2) && (r->disableFlag == 1)
////								&& (r->exec == 0)
////								&& (r->threadId != state.pthreadId)
////								&& (r->mutexAddr == q->mutexAddr)
////								&& (r->lockOrder > 0))
////						{
////							r->disableFlag = 0;
////							ei->pre = r;
////							r = NULL;
////							break;
////						}
////						r = r->next;
////					}
////
////				}
////
////				p = NULL;
////				q = NULL;
//				ei->current = ei->current->next;
//
//				ref<Expr> base = eval(ki, 1, state).value;
//				ConstantExpr *CE = dyn_cast<ConstantExpr>(
//						eval(ki, 1, state).value);
//				uint64_t val = 0;
//				BasicBlock *parent = i->getParent();
//				Function *ff = parent->getParent();
//
//				if (CE != 0)
//				{
//					val = CE->getZExtValue();
//					//cc
//					state.processInfo->callMutexUnlock(state, val);
//					//cc
//					MutexInfo *mutex = NULL;
//					for (aa = 0; aa < this->mutexinfolist.size(); aa++)
//					{
//						int tmpmutex = mutexinfolist[aa]->getMutex();
//						if (tmpmutex == val)
//						{
//							mutex = mutexinfolist[aa];
//							break;
//						}
//					}
//					//hlm
//
//					ExecutionSnapShot *snapshot = NULL;
//
//					for (unsigned int aa = 0; aa < state.snapShotList.size();
//							aa++)
//					{
//						snapshot = state.snapShotList[aa];
//						if (snapshot->mutex == val)
//						{
//							//						state.snapShotList.erase(
//							//								state.snapShotList.begin() + aa);
//							break;
//						}
//					}
//				}
////				std::cout << "线程：" << state.pthreadId << ",路径：" << state.pathId
////						<< ",state:" << &state << ",进行unlock操作结束\n";
//			}
//			else
//			{
////				std::cout << "state的线程号为:" << state.pthreadId << ",路径号为："
////						<< state.pathId << std::endl;
////				std::cout << "current的线程号为:" << ei->current->threadId
////						<< ",路径号为:" << ei->pathId << std::endl;
//
//				struct exePthreadInfo *p;
//				if (ei->current->disableFlag == 1) //当前current指针已经指示处于等待的线程，所以本state可以不等待这个执行结束，否则容易产生死锁
//				{
//					p = ei->current;
//					while (p->disableFlag == 1)
//						p = p->next;
//					if (p->threadId != state.pthreadId) //可以執行的线程不是本线程，则等待该线程执行结束
//					{
//						state.isWait = 1;
//						p->waitForExecutionStates.push_back(&state);
////						std::cout << "线程:" << state.pthreadId << ",路径:"
////								<< state.pathId << ",state:" << &state
////								<< "进入等待状态\n";
//					}
//					else
//					{
//						state.pc = state.prevPC;
//					}
//				}
//				else
//				{
//					state.isWait = 1;
//					ei->current->waitForExecutionStates.push_back(&state);
////					std::cout << "线程:" << state.pthreadId << ",路径:"
////							<< state.pathId << ",state:" << &state
////							<< "进入等待状态\n";
//				}
//			}
//		}
//		else
//		{
//			if (current == NULL)
//			{
////				printf("当前指针为NULL\n");
//				return;
//			}
//			else
//			{
////				std::cout << "state的线程号为:" << state.pthreadId << ",路径为："
////						<< state.pathId << std::endl;
////				std::cout << "current的线程号为:" << ei->current->threadId << ",路径为:"
////						<< ei->pathId << ",操作类型为:" << ei->current->type
////						<< std::endl;
//
//				struct exePthreadInfo *p;
//				if (ei->current->disableFlag == 1) //当前current指针已经指示处于等待的线程，所以本state可以不等待这个执行结束，否则容易产生死锁
//				{
//					p = ei->current;
//					while (p->disableFlag == 1)
//						p = p->next;
//					if (p->threadId != state.pthreadId) //可以執行的线程不是本线程，则等待该线程执行结束
//					{
//						state.isWait = 1;
//						p->waitForExecutionStates.push_back(&state);
////						std::cout << "线程:" << state.pthreadId << ",路径:"
////								<< state.pathId << ",state:" << &state
////								<< "进入等待状态\n";
//					}
//					else
//					{
//						state.pc = state.prevPC;
//					}
//				}
//				else
//				{
//					state.isWait = 1;
//					ei->current->waitForExecutionStates.push_back(&state);
////					std::cout << "线程:" << state.pthreadId << ",路径:"
////							<< state.pathId << ",state:" << &state
////							<< "进入等待状态\n";
//				}
//			}
//		}
//	}
//	else
//	{
//		ref<Expr> base = eval(ki, 1, state).value;
//		ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
//		uint64_t val = 0;
//		BasicBlock *parent = i->getParent();
//		Function *ff = parent->getParent();
//
//		if (CE != 0)
//		{
//			val = CE->getZExtValue();
//			//cc
//			state.processInfo->callMutexUnlock(state, val);
//			//PC
//			MutexInfo *mutex = NULL;
//			for (aa = 0; aa < this->mutexinfolist.size(); aa++)
//			{
//				int tmpmutex = mutexinfolist[aa]->getMutex();
//				if (tmpmutex == val)
//				{
//					mutex = mutexinfolist[aa];
//					break;
//				}
//			}
//			//hlm
//
//			for (aa = 0; aa < state.ownMutexList.size(); aa++)
//			{
//				int tmpMu = state.ownMutexList[aa];
//				if (tmpMu == val)
//				{
//					break;
//				}
//			}
//
//			state.ownMutexList.erase(state.ownMutexList.begin() + aa);
//
//			ExecutionSnapShot *snapshot = NULL;
//
//			for (aa = 0; aa < state.snapShotList.size(); aa++)
//			{
//				snapshot = state.snapShotList[aa];
//				if (snapshot->mutex == val)
//				{
//					//						state.snapShotList.erase(
//					//								state.snapShotList.begin() + aa);
//					break;
//				}
//			}
//		}
////		std::cout << "线程：" << state.pthreadId << ",路径：" << state.pathId
////				<< ",state:" << &state << ",进行unlock操作结束\n";
//	}
//}

//读/写锁
void Executor::call_pthread_rwlock_init(ExecutionState &state, KInstruction* ki,
		Instruction* i, unsigned numArgs, Value* fp, Function* f,
		std::vector<ref<Expr> > &arguments) {

}

void Executor::call_pthread_rwlock_destroy(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {

}

//加读锁
void Executor::call_pthread_rwlock_rdlock(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {
	ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
	uint64_t val = 0;
	if (CE != 0) {
		val = CE->getZExtValue();
		///cc,lock operate
		state.processInfo->callRdLock(state, val);
	}
}

//尝试加读锁
void Executor::call_pthread_rwlock_tryrdlock(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {
	ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
	uint64_t val = 0;
	if (CE != 0) {
		val = CE->getZExtValue();
		///cc,lock operate
		if (state.processInfo->callTryRdLock(state, val)) {
			return_value_handle(state, 0);
		} else {
			return_value_handle(state, -1);
		}
	}
}

//加写锁
void Executor::call_pthread_rwlock_wrlock(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {
	ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
	uint64_t val = 0;
	if (CE != 0) {
		val = CE->getZExtValue();
		///cc,lock operate
		state.processInfo->callWrLock(state, val);
	}
}

//尝试加写锁
void Executor::call_pthread_rwlock_trywrlock(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {
	ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
	uint64_t val = 0;
	if (CE != 0) {
		val = CE->getZExtValue();
		///cc,lock operate
		state.processInfo->callTryWrLock(state, val);
	}
}

//解锁读/写锁
void Executor::call_pthread_rwlock_unlock(ExecutionState &state,
		KInstruction* ki, Instruction* i, unsigned numArgs, Value* fp,
		Function* f, std::vector<ref<Expr> > &arguments) {
	ConstantExpr *CE = dyn_cast<ConstantExpr>(eval(ki, 1, state).value);
	uint64_t val = 0;
	if (CE != 0) {
		val = CE->getZExtValue();
		///cc,unlock operate
		if (state.processInfo->callRwUnlock(state, val)) {
			return_value_handle(state, 0);
		} else {
			return_value_handle(state, -1);
		}
	}
}

Executor::Executor(const InterpreterOptions &opts, InterpreterHandler *ih) :
		Interpreter(opts), kmodule(0), interpreterHandler(ih), searcher(0), externalDispatcher(
				new ExternalDispatcher()), statsTracker(0), pathWriter(
				0), symPathWriter(0), specialFunctionHandler(0), processTree(
				0), replayOut(0), replayPath(0), usingSeeds(0), atMemoryLimit(
				false), inhibitForking(false), haltExecution(false), ivcEnabled(
				false), isRollBack(0), exeLockOrder(1), isMonitor(0), RollBack(
				0), backExe(0), stpTimeout(
				MaxSTPTime != 0 && MaxInstructionTime != 0 ?
						std::min(MaxSTPTime, MaxInstructionTime) :
						std::max(MaxSTPTime, MaxInstructionTime)) {
//线程库函数处理函数初始化
	pthreadHandles[0] = new PthreadHandle("pthread_create",
			&Executor::call_pthread_create);
	pthreadHandles[1] = new PthreadHandle("pthread_exit",
			&Executor::call_pthread_exit);
	pthreadHandles[2] = new PthreadHandle("pthread_detach",
			&Executor::call_pthread_detach);
	pthreadHandles[3] = new PthreadHandle("pthread_join",
			&Executor::call_pthread_join);
	pthreadHandles[4] = new PthreadHandle("pthread_cancel",
			&Executor::call_pthread_cancel);

	pthreadHandles[5] = new PthreadHandle("pthread_mutex_init",
			&Executor::call_pthread_mutex_init);
	pthreadHandles[6] = new PthreadHandle("pthread_mutex_destroy",
			&Executor::call_pthread_mutex_destroy);
	pthreadHandles[7] = new PthreadHandle("pthread_mutex_lock",
			&Executor::call_pthread_mutex_lock);
	pthreadHandles[8] = new PthreadHandle("pthread_mutex_trylock",
			&Executor::call_pthread_mutex_trylock);
	pthreadHandles[9] = new PthreadHandle("pthread_mutex_unlock",
			&Executor::call_pthread_mutex_unlock);

	pthreadHandles[10] = new PthreadHandle("pthread_rwlock_init",
			&Executor::call_pthread_rwlock_init);
	pthreadHandles[11] = new PthreadHandle("pthread_rwlock_destroy",
			&Executor::call_pthread_rwlock_destroy);
	pthreadHandles[12] = new PthreadHandle("pthread_rwlock_rdlock",
			&Executor::call_pthread_rwlock_rdlock);
	pthreadHandles[13] = new PthreadHandle("pthread_rwlock_tryrdlock",
			&Executor::call_pthread_rwlock_tryrdlock);
	pthreadHandles[14] = new PthreadHandle("pthread_rwlock_wrlock",
			&Executor::call_pthread_rwlock_wrlock);
	pthreadHandles[15] = new PthreadHandle("pthread_rwlock_trywrlock",
			&Executor::call_pthread_rwlock_trywrlock);
	pthreadHandles[16] = new PthreadHandle("pthread_rwlock_unlock",
			&Executor::call_pthread_rwlock_unlock);

	if (stpTimeout)
		UseForkedSTP = true;
	STPSolver *stpSolver = new STPSolver(UseForkedSTP, STPOptimizeDivides);
	Solver *solver = constructSolverChain(stpSolver,
			interpreterHandler->getOutputFilename(
					ALL_QUERIES_SMT2_FILE_NAME),
			interpreterHandler->getOutputFilename(
					SOLVER_QUERIES_SMT2_FILE_NAME),
			interpreterHandler->getOutputFilename(
					ALL_QUERIES_PC_FILE_NAME),
			interpreterHandler->getOutputFilename(
					SOLVER_QUERIES_PC_FILE_NAME));

	this->solver = new TimingSolver(solver, stpSolver);

	memory = new MemoryManager();
}

const Module *Executor::setModule(llvm::Module *module,
		const ModuleOptions &opts) {
	assert(!kmodule && module && "can only register one module");
// XXX gross

	kmodule = new KModule(module);

// Initialize the context.
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
	TargetData *TD = kmodule->targetData;
#else
	DataLayout *TD = kmodule->targetData;
#endif
	Context::initialize(TD->isLittleEndian(),
			(Expr::Width) TD->getPointerSizeInBits());

	specialFunctionHandler = new SpecialFunctionHandler(*this);

	specialFunctionHandler->prepare();
	kmodule->prepare(opts, interpreterHandler);
	specialFunctionHandler->bind();

	if (StatsTracker::useStatistics()) {
		statsTracker = new StatsTracker(*this,
				interpreterHandler->getOutputFilename("assembly.ll"),
				userSearcherRequiresMD2U());
	}

	return module;
}

Executor::~Executor() {
	delete memory;
	delete externalDispatcher;
	if (processTree)
		delete processTree;
	if (specialFunctionHandler)
		delete specialFunctionHandler;
	if (statsTracker)
		delete statsTracker;
	delete solver;
	delete kmodule;
}

/***/

void Executor::initializeGlobalObject(ExecutionState &state, ObjectState *os,
		const Constant *c, unsigned offset) {
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
	TargetData *targetData = kmodule->targetData;
#else
	DataLayout *targetData = kmodule->targetData;
#endif
	if (const ConstantVector *cp = dyn_cast<ConstantVector>(c)) {
		unsigned elementSize = targetData->getTypeStoreSize(
				cp->getType()->getElementType());
		for (unsigned i = 0, e = cp->getNumOperands(); i != e; ++i)
			initializeGlobalObject(state, os, cp->getOperand(i),
					offset + i * elementSize);
	} else if (isa<ConstantAggregateZero>(c)) {
		unsigned i, size = targetData->getTypeStoreSize(c->getType());
		for (i = 0; i < size; i++)
			os->write8(offset + i, (uint8_t) 0);
	} else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)) {
		unsigned elementSize = targetData->getTypeStoreSize(
				ca->getType()->getElementType());
		for (unsigned i = 0, e = ca->getNumOperands(); i != e; ++i)
			initializeGlobalObject(state, os, ca->getOperand(i),
					offset + i * elementSize);
	} else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
		const StructLayout *sl = targetData->getStructLayout(
				cast<StructType>(cs->getType()));
		for (unsigned i = 0, e = cs->getNumOperands(); i != e; ++i)
			initializeGlobalObject(state, os, cs->getOperand(i),
					offset + sl->getElementOffset(i));
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
	}
	else if (const ConstantDataSequential *cds = dyn_cast
			< ConstantDataSequential > (c))
	{
		unsigned elementSize = targetData->getTypeStoreSize(
				cds->getElementType());
		for (unsigned i = 0, e = cds->getNumElements(); i != e; ++i)
		initializeGlobalObject(state, os, cds->getElementAsConstant(i),
				offset + i * elementSize);
#endif
	} else if (!isa<UndefValue>(c)) {
		unsigned StoreBits = targetData->getTypeStoreSizeInBits(
				c->getType());
		ref<ConstantExpr> C = evalConstant(c);

		// Extend the constant if necessary;
		assert(StoreBits >= C->getWidth() && "Invalid store size!");
		if (StoreBits > C->getWidth())
			C = C->ZExt(StoreBits);

		os->write(offset, C);
	}
}

MemoryObject * Executor::addExternalObject(ExecutionState &state, void *addr,
		unsigned size, bool isReadOnly) {
	MemoryObject *mo = memory->allocateFixed((uint64_t) (unsigned long) addr,
			size, 0);
	ObjectState *os = bindObjectInState(state, mo, false);
	for (unsigned i = 0; i < size; i++)
		os->write8(i, ((uint8_t*) addr)[i]);
	if (isReadOnly)
		os->setReadOnly(true);
	return mo;
}

extern void *__dso_handle __attribute__ ((__weak__));

void Executor::initializeGlobals(ExecutionState &state) {
	Module *m = kmodule->module;

	if (m->getModuleInlineAsm() != "")
		klee_warning("executable has module level assembly (ignoring)");

	assert(
			m->lib_begin() == m->lib_end() && "XXX do not support dependent libraries");

// represent function globals using the address of the actual llvm function
// object. given that we use malloc to allocate memory in states this also
// ensures that we won't conflict. we don't need to allocate a memory object
// since reading/writing via a function pointer is unsupported anyway.
	for (Module::iterator i = m->begin(), ie = m->end(); i != ie; ++i) {
		Function *f = i;
		ref<ConstantExpr> addr(0);

		// If the symbol has external weak linkage then it is implicitly
		// not defined in this module; if it isn't resolvable then it
		// should be null.
		if (f->hasExternalWeakLinkage()
				&& !externalDispatcher->resolveSymbol(f->getName())) {
			addr = Expr::createPointer(0);
		} else {
			addr = Expr::createPointer((unsigned long) (void*) f);
			legalFunctions.insert((uint64_t) (unsigned long) (void*) f);
		}

		globalAddresses.insert(std::make_pair(f, addr));
	}

// Disabled, we don't want to promote use of live externals.
#ifdef HAVE_CTYPE_EXTERNALS
#ifndef WINDOWS
#ifndef DARWIN
	/* From /usr/include/errno.h: it [errno] is a per-thread variable. */
	int *errno_addr = __errno_location();
	addExternalObject(state, (void *) errno_addr, sizeof *errno_addr, false);

	/* from /usr/include/ctype.h:
	 These point into arrays of 384, so they can be indexed by any `unsigned
	 char' value [0,255]; by EOF (-1); or by any `signed char' value
	 [-128,-1).  ISO C requires that the ctype functions work for `unsigned */
	const uint16_t **addr = __ctype_b_loc();
	addExternalObject(state, (void *) (*addr - 128), 384 * sizeof **addr,
			true);
	addExternalObject(state, addr, sizeof(*addr), true);

	const int32_t **lower_addr = __ctype_tolower_loc();
	addExternalObject(state, (void *) (*lower_addr - 128),
			384 * sizeof **lower_addr, true);
	addExternalObject(state, lower_addr, sizeof(*lower_addr), true);

	const int32_t **upper_addr = __ctype_toupper_loc();
	addExternalObject(state, (void *) (*upper_addr - 128),
			384 * sizeof **upper_addr, true);
	addExternalObject(state, upper_addr, sizeof(*upper_addr), true);
#endif
#endif
#endif

// allocate and initialize globals, done in two passes since we may
// need address of a global in order to initialize some other one.

// allocate memory objects for all globals
	for (Module::const_global_iterator i = m->global_begin(), e =
			m->global_end(); i != e; ++i) {
		if (i->isDeclaration()) {
			// FIXME: We have no general way of handling unknown external
			// symbols. If we really cared about making external stuff work
			// better we could support user definition, or use the EXE style
			// hack where we check the object file information.

			LLVM_TYPE_Q
			Type *ty = i->getType()->getElementType();
			uint64_t size = kmodule->targetData->getTypeStoreSize(ty);

			// XXX - DWD - hardcode some things until we decide how to fix.
#ifndef WINDOWS
			if (i->getName() == "_ZTVN10__cxxabiv117__class_type_infoE") {
				size = 0x2C;
			} else if (i->getName()
					== "_ZTVN10__cxxabiv120__si_class_type_infoE") {
				size = 0x2C;
			} else if (i->getName()
					== "_ZTVN10__cxxabiv121__vmi_class_type_infoE") {
				size = 0x2C;
			}
#endif

			if (size == 0) {
				llvm::errs()
						<< "Unable to find size for global variable: "
						<< i->getName()
						<< " (use will result in out of bounds access)\n";
			}

			MemoryObject *mo = memory->allocate(size, false, true, i);
			///cc,add global info to state
			state.processInfo->insertGlobal(mo->address, mo);
			ObjectState *os = bindObjectInState(state, mo, false);
			globalObjects.insert(std::make_pair(i, mo));
			globalAddresses.insert(std::make_pair(i, mo->getBaseExpr()));

			// Program already running = object already initialized.  Read
			// concrete value and write it to our copy.
			if (size) {
				void *addr;
				if (i->getName() == "__dso_handle") {
					addr = &__dso_handle; // wtf ?
				} else {
					addr = externalDispatcher->resolveSymbol(
							i->getName());
				}
				if (!addr)
					klee_error(
							"unable to load symbol(%s) while initializing globals.",
							i->getName().data());

				for (unsigned offset = 0; offset < mo->size; offset++)
					os->write8(offset,
							((unsigned char*) addr)[offset]);
			}
		} else {
			LLVM_TYPE_Q
			Type *ty = i->getType()->getElementType();
			uint64_t size = kmodule->targetData->getTypeStoreSize(ty);
			MemoryObject *mo = 0;

			if (UseAsmAddresses && i->getName()[0] == '\01') {
				char *end;
				uint64_t address = ::strtoll(
						i->getName().str().c_str() + 1, &end, 0);

				if (end && *end == '\0') {
					klee_message(
							"NOTE: allocated global at asm specified address: %#08llx"
									" (%llu bytes)",
							(long long) address,
							(unsigned long long) size);
					mo = memory->allocateFixed(address, size, &*i);
					mo->isUserSpecified = true; // XXX hack;
				}
			}

			if (!mo) {
				mo = memory->allocate(size, false, true, &*i);
				///cc,add global info to state
				state.processInfo->insertGlobal(mo->address, mo);
			}
			assert(mo && "out of memory");
			ObjectState *os = bindObjectInState(state, mo, false);
			globalObjects.insert(std::make_pair(i, mo));
			globalAddresses.insert(std::make_pair(i, mo->getBaseExpr()));

			if (!i->hasInitializer())
				os->initializeToRandom();
		}
	}

// link aliases to their definitions (if bound)
	for (Module::alias_iterator i = m->alias_begin(), ie = m->alias_end();
			i != ie; ++i) {
		// Map the alias to its aliasee's address. This works because we have
		// addresses for everything, even undefined functions.
		globalAddresses.insert(
				std::make_pair(i, evalConstant(i->getAliasee())));
	}

// once all objects are allocated, do the actual initialization
	for (Module::const_global_iterator i = m->global_begin(), e =
			m->global_end(); i != e; ++i) {
		if (i->hasInitializer()) {
			MemoryObject *mo = globalObjects.find(i)->second;
			const ObjectState *os = state.addressSpace.findObject(mo);
			assert(os);
			ObjectState *wos = state.addressSpace.getWriteable(mo, os);

			initializeGlobalObject(state, wos, i->getInitializer(), 0);
			// if(i->isConstant()) os->setReadOnly(true);
		}
	}
}

void Executor::branch(ExecutionState &state,
		const std::vector<ref<Expr> > &conditions,
		std::vector<ExecutionState*> &result) {
	TimerStatIncrementer timer(stats::forkTime);
	unsigned N = conditions.size();
	assert(N);

	stats::forks += N - 1;

// XXX do proper balance or keep random?
	result.push_back(&state);
	for (unsigned i = 1; i < N; ++i) {
		ExecutionState *es = result[theRNG.getInt32() % i];
		ExecutionState *ns = es->branch();
		addedStates.insert(ns);
		result.push_back(ns);
		es->ptreeNode->data = 0;
		std::pair<PTree::Node*, PTree::Node*> res = processTree->split(
				es->ptreeNode, ns, es);
		ns->ptreeNode = res.first;
		es->ptreeNode = res.second;
	}

// If necessary redistribute seeds to match conditions, killing
// states if necessary due to OnlyReplaySeeds (inefficient but
// simple).

	std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it =
			seedMap.find(&state);
	if (it != seedMap.end()) {
		std::vector<SeedInfo> seeds = it->second;
		seedMap.erase(it);

		// Assume each seed only satisfies one condition (necessarily true
		// when conditions are mutually exclusive and their conjunction is
		// a tautology).
		for (std::vector<SeedInfo>::iterator siit = seeds.begin(), siie =
				seeds.end(); siit != siie; ++siit) {
			unsigned i;
			for (i = 0; i < N; ++i) {
				ref<ConstantExpr> res;
				bool success = solver->getValue(state,
						siit->assignment.evaluate(conditions[i]),
						res);
				assert(success && "FIXME: Unhandled solver failure");
				(void) success;
				if (res->isTrue())
					break;
			}

			// If we didn't find a satisfying condition randomly pick one
			// (the seed will be patched).
			if (i == N)
				i = theRNG.getInt32() % N;

			seedMap[result[i]].push_back(*siit);
		}

		if (OnlyReplaySeeds) {
			for (unsigned i = 0; i < N; ++i) {
				if (!seedMap.count(result[i])) {
					terminateState(*result[i]);
					result[i] = NULL;
				}
			}
		}
	}

	for (unsigned i = 0; i < N; ++i)
		if (result[i])
			addConstraint(*result[i], conditions[i]);
}

Executor::StatePair Executor::fork(ExecutionState &current, ref<Expr> condition,
		bool isInternal) {
	Solver::Validity res;
	std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it =
			seedMap.find(&current);
	bool isSeeding = it != seedMap.end();

	if (!isSeeding && !isa<ConstantExpr>(condition)
			&& (MaxStaticForkPct != 1. || MaxStaticSolvePct != 1.
					|| MaxStaticCPForkPct != 1.
					|| MaxStaticCPSolvePct != 1.)
			&& statsTracker->elapsed() > 60.) {
		StatisticManager &sm = *theStatisticManager;
		CallPathNode *cpn = current.stack.back().callPathNode;
		if ((MaxStaticForkPct < 1.
				&& sm.getIndexedValue(stats::forks, sm.getIndex())
						> stats::forks * MaxStaticForkPct)
				|| (MaxStaticCPForkPct < 1. && cpn
						&& (cpn->statistics.getValue(stats::forks)
								> stats::forks
										* MaxStaticCPForkPct))
				|| (MaxStaticSolvePct < 1
						&& sm.getIndexedValue(stats::solverTime,
								sm.getIndex())
								> stats::solverTime
										* MaxStaticSolvePct)
				|| (MaxStaticCPForkPct < 1. && cpn
						&& (cpn->statistics.getValue(
								stats::solverTime)
								> stats::solverTime
										* MaxStaticCPSolvePct))) {
			ref<ConstantExpr> value;
			bool success = solver->getValue(current, condition, value);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			addConstraint(current, EqExpr::create(value, condition));
			condition = value;
		}
	}

	double timeout = stpTimeout;
	if (isSeeding)
		timeout *= it->second.size();
	solver->setTimeout(timeout);
	bool success = solver->evaluate(current, condition, res);
	solver->setTimeout(0);
	if (!success) {
		current.pc = current.prevPC;
		terminateStateEarly(current, "Query timed out (fork).");
		return StatePair(0, 0);
	}

	if (!isSeeding) {
		if (replayPath && !isInternal) {
			assert(
					replayPosition < replayPath->size() && "ran out of branches in replay path mode");
			bool branch = (*replayPath)[replayPosition++];

			if (res == Solver::True) {
				assert(
						branch && "hit invalid branch in replay path mode");
			} else if (res == Solver::False) {
				assert(
						!branch && "hit invalid branch in replay path mode");
			} else {
				// add constraints
				if (branch) {
					res = Solver::True;
					addConstraint(current, condition);
				} else {
					res = Solver::False;
					addConstraint(current,
							Expr::createIsZero(condition));
				}
			}
		} else if (res == Solver::Unknown) {
			assert(
					!replayOut && "in replay mode, only one branch can be true.");

			if ((MaxMemoryInhibit && atMemoryLimit)
					|| current.forkDisabled || inhibitForking
					|| (MaxForks != ~0u && stats::forks >= MaxForks)) {

				if (MaxMemoryInhibit && atMemoryLimit)
					klee_warning_once(0,
							"skipping fork (memory cap exceeded)");
				else if (current.forkDisabled)
					klee_warning_once(0,
							"skipping fork (fork disabled on current path)");
				else if (inhibitForking)
					klee_warning_once(0,
							"skipping fork (fork disabled globally)");
				else
					klee_warning_once(0,
							"skipping fork (max-forks reached)");

				TimerStatIncrementer timer(stats::forkTime);
				if (theRNG.getBool()) {
					addConstraint(current, condition);
					res = Solver::True;
				} else {
					addConstraint(current,
							Expr::createIsZero(condition));
					res = Solver::False;
				}
			}
		}
	}

// Fix branch in only-replay-seed mode, if we don't have both true
// and false seeds.
	if (isSeeding && (current.forkDisabled || OnlyReplaySeeds)
			&& res == Solver::Unknown) {
		bool trueSeed = false, falseSeed = false;
		// Is seed extension still ok here?
		for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
				siie = it->second.end(); siit != siie; ++siit) {
			ref<ConstantExpr> res;
			bool success = solver->getValue(current,
					siit->assignment.evaluate(condition), res);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			if (res->isTrue()) {
				trueSeed = true;
			} else {
				falseSeed = true;
			}
			if (trueSeed && falseSeed)
				break;
		}
		if (!(trueSeed && falseSeed)) {
			assert(trueSeed || falseSeed);

			res = trueSeed ? Solver::True : Solver::False;
			addConstraint(current,
					trueSeed ? condition : Expr::createIsZero(
									condition));
		}
	}

// XXX - even if the constraint is provable one way or the other we
// can probably benefit by adding this constraint and allowing it to
// reduce the other constraints. For example, if we do a binary
// search on a particular value, and then see a comparison against
// the value it has been fixed at, we should take this as a nice
// hint to just use the single constraint instead of all the binary
// search ones. If that makes sense.
	if (res == Solver::True) {
		if (!isInternal) {
			if (pathWriter) {
				current.pathOS << "1";
			}
		}

		return StatePair(&current, 0);
	} else if (res == Solver::False) {
		if (!isInternal) {
			if (pathWriter) {
				current.pathOS << "0";
			}
		}

		return StatePair(0, &current);
	} else {
		//产生新的state
		TimerStatIncrementer timer(stats::forkTime);
		ExecutionState *falseState, *trueState = &current;

		++stats::forks;

		falseState = trueState->branch();
		addedStates.insert(falseState);

		if (RandomizeFork && theRNG.getBool())
			std::swap(trueState, falseState);

		if (it != seedMap.end()) {
			std::vector<SeedInfo> seeds = it->second;
			it->second.clear();
			std::vector<SeedInfo> &trueSeeds = seedMap[trueState];
			std::vector<SeedInfo> &falseSeeds = seedMap[falseState];
			for (std::vector<SeedInfo>::iterator siit = seeds.begin(),
					siie = seeds.end(); siit != siie; ++siit) {
				ref<ConstantExpr> res;
				bool success = solver->getValue(current,
						siit->assignment.evaluate(condition), res);
				assert(success && "FIXME: Unhandled solver failure");
				(void) success;
				if (res->isTrue()) {
					trueSeeds.push_back(*siit);
				} else {
					falseSeeds.push_back(*siit);
				}
			}

			bool swapInfo = false;
			if (trueSeeds.empty()) {
				if (&current == trueState)
					swapInfo = true;
				seedMap.erase(trueState);
			}
			if (falseSeeds.empty()) {
				if (&current == falseState)
					swapInfo = true;
				seedMap.erase(falseState);
			}
			if (swapInfo) {
				std::swap(trueState->coveredNew,
						falseState->coveredNew);
				std::swap(trueState->coveredLines,
						falseState->coveredLines);
			}
		}

		current.ptreeNode->data = 0;
		std::pair<PTree::Node*, PTree::Node*> res = processTree->split(
				current.ptreeNode, falseState, trueState);
		falseState->ptreeNode = res.first;
		trueState->ptreeNode = res.second;

		if (!isInternal) {
			if (pathWriter) {
				falseState->pathOS = pathWriter->open(current.pathOS);
				trueState->pathOS << "1";
				falseState->pathOS << "0";
			}
			if (symPathWriter) {
				falseState->symPathOS = symPathWriter->open(
						current.symPathOS);
				trueState->symPathOS << "1";
				falseState->symPathOS << "0";
			}
		}

		addConstraint(*trueState, condition);
		addConstraint(*falseState, Expr::createIsZero(condition));

		// Kinda gross, do we even really still want this option?
		if (MaxDepth && MaxDepth <= trueState->depth) {
			terminateStateEarly(*trueState, "max-depth exceeded.");
			terminateStateEarly(*falseState, "max-depth exceeded.");
			return StatePair(0, 0);
		}

		return StatePair(trueState, falseState);
	}
}

void Executor::addConstraint(ExecutionState &state, ref<Expr> condition) {
	if (ConstantExpr * CE = dyn_cast<ConstantExpr>(condition)) {
		assert(CE->isTrue() && "attempt to add invalid constraint");
		return;
	}

// Check to see if this constraint violates seeds.
	std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it =
			seedMap.find(&state);
	if (it != seedMap.end()) {
		bool warn = false;
		for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
				siie = it->second.end(); siit != siie; ++siit) {
			bool res;
			bool success = solver->mustBeFalse(state,
					siit->assignment.evaluate(condition), res);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			if (res) {
				siit->patchSeed(state, condition, solver);
				warn = true;
			}
		}
		if (warn)
			klee_warning("seeds patched for violating constraint");
	}

	state.addConstraint(condition);
	if (ivcEnabled)
		doImpliedValueConcretization(state, condition,
				ConstantExpr::alloc(1, Expr::Bool));
}

ref<klee::ConstantExpr> Executor::evalConstant(const Constant *c) {
	if (const llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
		return evalConstantExpr(ce);
	} else {
		if (const ConstantInt *ci = dyn_cast<ConstantInt>(c)) {
			return ConstantExpr::alloc(ci->getValue());
		} else if (const ConstantFP *cf = dyn_cast<ConstantFP>(c)) {
			return ConstantExpr::alloc(cf->getValueAPF().bitcastToAPInt());
		} else if (const GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
			return globalAddresses.find(gv)->second;
		} else if (isa<ConstantPointerNull>(c)) {
			return Expr::createPointer(0);
		} else if (isa<UndefValue>(c) || isa<ConstantAggregateZero>(c)) {
			return ConstantExpr::create(0,
					getWidthForLLVMType(c->getType()));
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
		}
		else if (const ConstantDataSequential *cds = dyn_cast
				< ConstantDataSequential > (c))
		{
			std::vector < ref<Expr> > kids;
			for (unsigned i = 0, e = cds->getNumElements(); i != e; ++i)
			{
				ref < Expr > kid = evalConstant(cds->getElementAsConstant(i));
				kids.push_back(kid);
			}
			ref < Expr > res = ConcatExpr::createN(kids.size(), kids.data());
			return cast < ConstantExpr > (res);
#endif
		} else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
			const StructLayout *sl = kmodule->targetData->getStructLayout(
					cs->getType());
			llvm::SmallVector<ref<Expr>, 4> kids;
			for (unsigned i = cs->getNumOperands(); i != 0; --i) {
				unsigned op = i - 1;
				ref<Expr> kid = evalConstant(cs->getOperand(op));

				uint64_t thisOffset = sl->getElementOffsetInBits(op),
						nextOffset =
								(op == cs->getNumOperands() - 1) ?
										sl->getSizeInBits() :
										sl->getElementOffsetInBits(
												op + 1);
				if (nextOffset - thisOffset > kid->getWidth()) {
					uint64_t paddingWidth = nextOffset - thisOffset
							- kid->getWidth();
					kids.push_back(
							ConstantExpr::create(0,
									paddingWidth));
				}

				kids.push_back(kid);
			}
			ref<Expr> res = ConcatExpr::createN(kids.size(), kids.data());
			return cast<ConstantExpr>(res);
		} else {
			// Constant{Array,Vector}
			assert(0 && "invalid argument to evalConstant()");
		}
	}
}

const Cell& Executor::eval(KInstruction *ki, unsigned index,
		ExecutionState &state) const {
	assert(index < ki->inst->getNumOperands());
	int vnumber = ki->operands[index];

	assert(
			vnumber != -1 && "Invalid operand to eval(), not a value or constant!");

// Determine if this is a constant or not.
	if (vnumber < 0) {
		unsigned index = -vnumber - 2;
		return kmodule->constantTable[index];
	} else {
		unsigned index = vnumber;
		StackFrame &sf = state.stack.back();
		return sf.locals[index];
	}
}

void Executor::bindLocal(KInstruction *target, ExecutionState &state,
		ref<Expr> value) {
	getDestCell(state, target).value = value;
}

void Executor::bindArgument(KFunction *kf, unsigned index,
		ExecutionState &state, ref<Expr> value) {
	getArgumentCell(state, kf, index).value = value;
}

ref<Expr> Executor::toUnique(const ExecutionState &state, ref<Expr> &e) {
	ref<Expr> result = e;

	if (!isa<ConstantExpr>(e)) {
		ref<ConstantExpr> value;
		bool isTrue = false;

		solver->setTimeout(stpTimeout);
		if (solver->getValue(state, e, value)
				&& solver->mustBeTrue(state, EqExpr::create(e, value),
						isTrue) && isTrue)
			result = value;
		solver->setTimeout(0);
	}

	return result;
}

/* Concretize the given expression, and return a possible constant value.
 'reason' is just a documentation string stating the reason for concretization. */
ref<klee::ConstantExpr> Executor::toConstant(ExecutionState &state, ref<Expr> e,
		const char *reason) {
	e = state.constraints.simplifyExpr(e);
	if (ConstantExpr * CE = dyn_cast<ConstantExpr>(e))
		return CE;

	ref<ConstantExpr> value;
	bool success = solver->getValue(state, e, value);
	assert(success && "FIXME: Unhandled solver failure");
	(void) success;

	std::ostringstream os;
	os << "silently concretizing (reason: " << reason << ") expression " << e
			<< " to value " << value << " (" << (*(state.pc)).info->file
			<< ":" << (*(state.pc)).info->line << ")";

	if (AllExternalWarnings)
		klee_warning(reason, os.str().c_str());
	else
		klee_warning_once(reason, "%s", os.str().c_str());

	addConstraint(state, EqExpr::create(e, value));

	return value;
}

void Executor::executeGetValue(ExecutionState &state, ref<Expr> e,
		KInstruction *target) {
	e = state.constraints.simplifyExpr(e);
	std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it =
			seedMap.find(&state);
	if (it == seedMap.end() || isa<ConstantExpr>(e)) {
		ref<ConstantExpr> value;
		bool success = solver->getValue(state, e, value);
		assert(success && "FIXME: Unhandled solver failure");
		(void) success;
		bindLocal(target, state, value);
	} else {
		std::set<ref<Expr> > values;
		for (std::vector<SeedInfo>::iterator siit = it->second.begin(),
				siie = it->second.end(); siit != siie; ++siit) {
			ref<ConstantExpr> value;
			bool success = solver->getValue(state,
					siit->assignment.evaluate(e), value);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			values.insert(value);
		}

		std::vector<ref<Expr> > conditions;
		for (std::set<ref<Expr> >::iterator vit = values.begin(), vie =
				values.end(); vit != vie; ++vit)
			conditions.push_back(EqExpr::create(e, *vit));

		std::vector<ExecutionState*> branches;
		branch(state, conditions, branches);

		std::vector<ExecutionState*>::iterator bit = branches.begin();
		for (std::set<ref<Expr> >::iterator vit = values.begin(), vie =
				values.end(); vit != vie; ++vit) {
			ExecutionState *es = *bit;
			if (es)
				bindLocal(target, *es, *vit);
			++bit;
		}
	}
}

void Executor::stepInstruction(ExecutionState &state) {

	if (DebugPrintInstructions) {
		printFileLine(state, state.pc);
		std::cerr << std::setw(10) << stats::instructions << " ";
		llvm::errs() << *(state.pc->inst) << '\n';
	}

	if (statsTracker)
		statsTracker->stepInstruction(state);

	++stats::instructions;
	state.prevPC = state.pc;
	++state.pc;

	if (stats::instructions == StopAfterNInstructions)
		haltExecution = true;
}

void Executor::executeCall(ExecutionState &state, KInstruction *ki, Function *f,
		std::vector<ref<Expr> > &arguments) {
	Instruction *i = ki->inst;
	if (f && f->isDeclaration()) {
		switch (f->getIntrinsicID()) {
		case Intrinsic::not_intrinsic:
			// state may be destroyed by this call, cannot touch
			callExternalFunction(state, ki, f, arguments);
			break;

			// va_arg is handled by caller and intrinsic lowering, see comment for
			// ExecutionState::varargs
		case Intrinsic::vastart: {
			StackFrame &sf = state.stack.back();
			assert(
					sf.varargs && "vastart called in function with no vararg object");

			// FIXME: This is really specific to the architecture, not the pointer
			// size. This happens to work fir x86-32 and x86-64, however.
			Expr::Width WordSize = Context::get().getPointerWidth();
			if (WordSize == Expr::Int32) {
				executeMemoryOperation(state, true, arguments[0],
						sf.varargs->getBaseExpr(), 0);
			} else {
				assert(WordSize == Expr::Int64 && "Unknown word size!");

				// X86-64 has quite complicated calling convention. However,
				// instead of implementing it, we can do a simple hack: just
				// make a function believe that all varargs are on stack.
				executeMemoryOperation(state, true, arguments[0],
						ConstantExpr::create(48, 32), 0); // gp_offset
				executeMemoryOperation(state, true,
						AddExpr::create(arguments[0],
								ConstantExpr::create(4, 64)),
						ConstantExpr::create(304, 32), 0); // fp_offset
				executeMemoryOperation(state, true,
						AddExpr::create(arguments[0],
								ConstantExpr::create(8, 64)),
						sf.varargs->getBaseExpr(), 0); // overflow_arg_area
				executeMemoryOperation(state, true,
						AddExpr::create(arguments[0],
								ConstantExpr::create(16, 64)),
						ConstantExpr::create(0, 64), 0); // reg_save_area
			}
			break;
		}
		case Intrinsic::vaend:
			// va_end is a noop for the interpreter.
			//
			// FIXME: We should validate that the target didn't do something bad
			// with vaeend, however (like call it twice).
			break;

		case Intrinsic::vacopy:
			// va_copy should have been lowered.
			//
			// FIXME: It would be nice to check for errors in the usage of this as
			// well.
		default:
			klee_error("unknown intrinsic: %s", f->getName().data());
		}

		if (InvokeInst * ii = dyn_cast<InvokeInst>(i))
			transferToBasicBlock(ii->getNormalDest(), i->getParent(),
					state);
	} else {
		// FIXME: I'm not really happy about this reliance on prevPC but it is ok, I
		// guess. This just done to avoid having to pass KInstIterator everywhere
		// instead of the actual instruction, since we can't make a KInstIterator
		// from just an instruction (unlike LLVM).

		//hlm
		if (state.isMain == 0) {
			state.sumFunc++;
		}
		//hlm

		KFunction *kf = kmodule->functionMap[f];
		state.pushFrame(state.prevPC, kf);
		state.pc = kf->instructions;

		if (statsTracker)
			statsTracker->framePushed(state,
					&state.stack[state.stack.size() - 2]);

		// TODO: support "byval" parameter attribute
		// TODO: support zeroext, signext, sret attributes

		unsigned callingArgs = arguments.size();
		unsigned funcArgs = f->arg_size();
		if (!f->isVarArg()) {
			if (callingArgs > funcArgs) {
				klee_warning_once(f, "calling %s with extra arguments.",
						f->getName().data());
			} else if (callingArgs < funcArgs) {
				terminateStateOnError(state,
						"calling function with too few arguments",
						"user.err");
				return;
			}
		} else {
			if (callingArgs < funcArgs) {
				terminateStateOnError(state,
						"calling function with too few arguments",
						"user.err");
				return;
			}

			StackFrame &sf = state.stack.back();
			unsigned size = 0;
			for (unsigned i = funcArgs; i < callingArgs; i++) {
				// FIXME: This is really specific to the architecture, not the pointer
				// size. This happens to work fir x86-32 and x86-64, however.
				Expr::Width WordSize = Context::get().getPointerWidth();
				if (WordSize == Expr::Int32) {
					size += Expr::getMinBytesForWidth(
							arguments[i]->getWidth());
				} else {
					size += llvm::RoundUpToAlignment(
							arguments[i]->getWidth(), WordSize)
							/ 8;
				}
			}

			MemoryObject *mo = sf.varargs = memory->allocate(size, true,
					false, state.prevPC->inst);
			if (!mo) {
				terminateStateOnExecError(state,
						"out of memory (varargs)");
				return;
			}
			ObjectState *os = bindObjectInState(state, mo, true);
			unsigned offset = 0;
			for (unsigned i = funcArgs; i < callingArgs; i++) {
				// FIXME: This is really specific to the architecture, not the pointer
				// size. This happens to work fir x86-32 and x86-64, however.
				Expr::Width WordSize = Context::get().getPointerWidth();
				if (WordSize == Expr::Int32) {
					os->write(offset, arguments[i]);
					offset += Expr::getMinBytesForWidth(
							arguments[i]->getWidth());
				} else {
					assert(
							WordSize == Expr::Int64 && "Unknown word size!");
					os->write(offset, arguments[i]);
					offset += llvm::RoundUpToAlignment(
							arguments[i]->getWidth(), WordSize)
							/ 8;
				}
			}
		}

		unsigned numFormals = f->arg_size();
		for (unsigned i = 0; i < numFormals; ++i)
			bindArgument(kf, i, state, arguments[i]);
	}
}

void Executor::transferToBasicBlock(BasicBlock *dst, BasicBlock *src,
		ExecutionState &state) {
// Note that in general phi nodes can reuse phi values from the same
// block but the incoming value is the eval() result *before* the
// execution of any phi nodes. this is pathological and doesn't
// really seem to occur, but just in case we run the PhiCleanerPass
// which makes sure this cannot happen and so it is safe to just
// eval things in order. The PhiCleanerPass also makes sure that all
// incoming blocks have the same order for each PHINode so we only
// have to compute the index once.
//
// With that done we simply set an index in the state so that PHI
// instructions know which argument to eval, set the pc, and continue.

// XXX this lookup has to go ?
	KFunction *kf = state.stack.back().kf;
	unsigned entry = kf->basicBlockEntry[dst];
	state.pc = &kf->instructions[entry];
	if (state.pc->inst->getOpcode() == Instruction::PHI) {
		PHINode *first = static_cast<PHINode*>(state.pc->inst);
		state.incomingBBIndex = first->getBasicBlockIndex(src);
	}
}

void Executor::printFileLine(ExecutionState &state, KInstruction *ki) {
	const InstructionInfo &ii = *ki->info;

	if (ii.file != "")
		std::cerr << "     " << ii.file << ":" << ii.line << ":";
	else
		std::cerr << "     [no debug info]:";
}

/// Compute the true target of a function call, resolving LLVM and KLEE aliases
/// and bitcasts.
Function* Executor::getTargetFunction(Value *calledVal, ExecutionState &state) {
	SmallPtrSet<const GlobalValue*, 3> Visited;

	Constant *c = dyn_cast<Constant>(calledVal);
	if (!c)
		return 0;

	while (true) {
		if (GlobalValue * gv = dyn_cast<GlobalValue>(c)) {
			if (!Visited.insert(gv))
				return 0;

			std::string alias = state.getFnAlias(gv->getName());
			if (alias != "") {
				llvm::Module* currModule = kmodule->module;
				GlobalValue *old_gv = gv;
				gv = currModule->getNamedValue(alias);
				if (!gv) {
					llvm::errs() << "Function " << alias
							<< "(), alias for "
							<< old_gv->getName()
							<< " not found!\n";
					assert(0 && "function alias not found");
				}
			}

			if (Function * f = dyn_cast<Function>(gv))
				return f;
			else if (GlobalAlias * ga = dyn_cast<GlobalAlias>(gv))
				c = ga->getAliasee();
			else
				return 0;
		} else if (llvm::ConstantExpr * ce = dyn_cast<llvm::ConstantExpr>(
				c)) {
			if (ce->getOpcode() == Instruction::BitCast)
				c = ce->getOperand(0);
			else
				return 0;
		} else
			return 0;
	}
}

static bool isDebugIntrinsic(const Function *f, KModule *KM) {
#if LLVM_VERSION_CODE < LLVM_VERSION(2, 7)
// Fast path, getIntrinsicID is slow.
	if (f == KM->dbgStopPointFn)
	return true;

	switch (f->getIntrinsicID())
	{
		case Intrinsic::dbg_stoppoint:
		case Intrinsic::dbg_region_start:
		case Intrinsic::dbg_region_end:
		case Intrinsic::dbg_func_start:
		case Intrinsic::dbg_declare:
		return true;

		default:
		return false;
	}
#else
	return false;
#endif
}

static inline const llvm::fltSemantics * fpWidthToSemantics(unsigned width) {
	switch (width) {
	case Expr::Int32:
		return &llvm::APFloat::IEEEsingle;
	case Expr::Int64:
		return &llvm::APFloat::IEEEdouble;
	case Expr::Fl80:
		return &llvm::APFloat::x87DoubleExtended;
	default:
		return 0;
	}
}

unsigned Executor::getSourceLine(llvm::DebugLoc dbg) {
	return dbg.getLine();
}

void Executor::executeInstruction(ExecutionState &state, KInstruction *ki) {

	unsigned aa = 0;
	Instruction *i = ki->inst;

//	printf("local = %d, source=%d\n",i->getDebugLoc().getCol(),getSourceLine(i->getDebugLoc()));
//	std::cout << "线程:" << state.pthreadId << ",路径:" << state.pathId << ",指令:"
//			<< i->getOpcodeName() << ",state为" << &state << std::endl;

	switch (i->getOpcode()) {
// Control flow
	case Instruction::Ret: {
		ReturnInst *ri = cast<ReturnInst>(i);
		KInstIterator kcaller = state.stack.back().caller;
		Instruction *caller = kcaller ? kcaller->inst : 0;
		bool isVoidReturn = (ri->getNumOperands() == 0);
		ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);

		if (!isVoidReturn) {
			result = eval(ki, 0, state).value;
		}

		if (state.isMain == 0) //不是主线程
				{
			//	std::cout<<"state.sumFunc="<<state.sumFunc<<std::endl;
			state.sumFunc--;
//			std::cout << "线程号为" << state.pthreadId << "路径号为" << state.pathId
//					<< "调用层数为" << state.sumFunc << std::endl;
			if (state.sumFunc == 0) //调用为0层，即子线程返回
					{
				state.exeInfo->isDead = 1;

				//hlm 遍历state测试线程是否已经结束
				int threadID = state.pthreadId;

				PthreadInfo *pthread = NULL;
				for (std::vector<PthreadInfo*>::iterator itp =
						threadList.begin(), iep = threadList.end();
						itp != iep; itp++) {

					pthread = *itp;
					if (pthread->threadId == threadID) {
						break;
					}
				}

				assert(pthread != NULL);

				ExecutionState *st = NULL;

				for (std::vector<ExecutionState*>::iterator it =
						pthread->waitExitStates.begin(), ie =
						pthread->waitExitStates.end(); it != ie;
						it++) {
					if (pthread->waitExitStates.size() != 0) {

						st = *it;
						assert((st != NULL) && "找不到等待的执行状态");
						assert(st->prevPC->inst != NULL);
						if (st->pathId == state.pathId) {

							CallSite css(st->prevPC->inst);
							Value *ffp = css.getCalledValue();
							Function *ff = getTargetFunction(ffp,
									state);
							assert(ff != NULL);
							KFunction *kff = new KFunction(ff,
									kmodule);
							assert(kff != NULL);
							KInstruction *kii = st->prevPC;
							ref<Expr> fpara =
									eval(kii, 2, *st).value;

							ConstantExpr *CE = dyn_cast<
									ConstantExpr>(fpara);
							uint64_t val = 0;
							if (CE != 0) {
								val = CE->getZExtValue();
								if (val != 0) {
									executeMemoryOperation(
											*st, true,
											fpara, result,
											kii);
								}
							}
							st->isWait = 0;

							pthread->waitExitStates.erase(it);
						}
					}
				}

				map<int, int>::iterator l_it;
				l_it = pthread->isAlives.find(state.pathId);
				if (l_it != pthread->isAlives.end()) {
					l_it->second = 0; //在这个域中结束
				}

				pthread->retExprs.insert(
						std::make_pair(state.pathId, result));
				///cc,call pthread exit
//				std::vector<ref<Expr> > arguments;
//				call_pthread_exit(state, ki, i, 1, NULL, NULL, arguments);

				terminateStateOnExit(state);
			}
		}

		//ssg

		if (state.stack.size() <= 1) {
			assert(!caller && "caller set on initial stack frame");
			state.exeInfo->isDead = 1;

			if (state.isMain == 0) {
				std::vector<ref<Expr> > arguments;
				call_pthread_exit(state, ki, i, 1, NULL, NULL,
						arguments);
			} else {
				terminateStateOnExit(state);
			}
		} else {
			state.popFrame();

			if (statsTracker)
				statsTracker->framePopped(state);

			if (InvokeInst * ii = dyn_cast<InvokeInst>(caller)) {
				transferToBasicBlock(ii->getNormalDest(),
						caller->getParent(), state);
			} else {
				state.pc = kcaller;
				++state.pc;
			}

			if (!isVoidReturn) {
				LLVM_TYPE_Q
				Type *t = caller->getType();
				if (t != Type::getVoidTy(getGlobalContext())) {
					// may need to do coercion due to bitcasts
					Expr::Width from = result->getWidth();
					Expr::Width to = getWidthForLLVMType(t);

					if (from != to) {
						CallSite cs =
								(isa<InvokeInst>(caller) ?
										CallSite(
												cast<
														InvokeInst>(
														caller)) :
										CallSite(
												cast<
														CallInst>(
														caller)));

						// XXX need to check other param attrs ?
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
						bool isSExt = cs.paramHasAttr(0,
								llvm::Attributes::SExt);
#else
						bool isSExt = cs.paramHasAttr(0,
								llvm::Attribute::SExt);
#endif
						if (isSExt) {
							result = SExtExpr::create(result, to);
						} else {
							result = ZExtExpr::create(result, to);
						}
					}

					bindLocal(kcaller, state, result);
				}
			} else {
				// We check that the return value has no users instead of
				// checking the type, since C defaults to returning int for
				// undeclared functions.
				if (!caller->use_empty()) {
					terminateStateOnExecError(state,
							"return void when caller expected a result");
				}
			}
		}

		break;
	}
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 1)
	case Instruction::Unwind: {
		for (;;) {
			KInstruction *kcaller = state.stack.back().caller;
			state.popFrame();

			if (statsTracker)
				statsTracker->framePopped(state);

			if (state.stack.empty()) {
				terminateStateOnExecError(state,
						"unwind from initial stack frame");
				break;
			} else {
				Instruction *caller = kcaller->inst;
				if (InvokeInst * ii = dyn_cast<InvokeInst>(caller)) {
					transferToBasicBlock(ii->getUnwindDest(),
							caller->getParent(), state);
					break;
				}
			}
		}
		break;
	}
#endif
	case Instruction::Br: {
		BranchInst *bi = cast<BranchInst>(i);

		if (bi->isUnconditional()) {
			transferToBasicBlock(bi->getSuccessor(0), bi->getParent(),
					state);
		}
//		else if (state.globalId != 0)
//		{ //ssg当遇到全局变量的判断语句时，也肯定需要产生分支
//			ExecutionState *continueState1, *newState1;
//			++stats::forks; //stats是state的链表，forks是state的个数
//			continueState1 = &state;
//			newState1 = state.branch();
//			newState1->pathId = ExecutionState::createPathId;
//			ExecutionState::createPathId++;
//
//			addedStates.insert(newState1);
//
//			state.ptreeNode->data = 0;
//			std::pair<PTree::Node*, PTree::Node*> res = processTree->split(
//					state.ptreeNode, continueState1, newState1); //processTress在state.ptreeNode这个节点上split
//			continueState1->ptreeNode = res.first;
//			newState1->ptreeNode = res.second;
//
//			if (newState1->exeInfo->exeInfo.back().constrainType == 1)
//			{
//				newState1->exeInfo->exeInfo.back().constrainType = 2;
//			}
//
//			std::vector<ExecutionInfo *> pathExe;
//			ExeInfo.push_back(pathExe);
//			std::vector<std::vector<ExecutionInfo *> >::iterator ee =
//					ExeInfo.begin();
//			ee = ee + newState1->pathId;
//			(*ee).push_back(newState1->exeInfo);
//
//			transferToBasicBlock(bi->getSuccessor(0), bi->getParent(),
//					*continueState1);
//			transferToBasicBlock(bi->getSuccessor(1), bi->getParent(),
//					*newState1);
//
//			//检查路径号与branches.first相同,但线程号不同的
//			std::set<ExecutionState *>::iterator zz = states.begin();
//
//			while (zz != states.end())
//			{
//				if (continueState1->pathId == (*zz)->pathId
//						&& continueState1->pthreadId != (*zz)->pthreadId)
//				{
//					ExecutionState *continueState, *newState;
//					++stats::forks; //stats是state的链表，forks是state的个数
//					continueState = (*zz);
//					newState = (*zz)->branch();
//					newState->pathId = newState1->pathId;
//					addedStates.insert(newState);
//
//					(*ee).push_back(newState->exeInfo);
//
//					(*zz)->ptreeNode->data = 0;
//					std::pair<PTree::Node*, PTree::Node*> res =
//							processTree->split((*zz)->ptreeNode, continueState,
//									newState); //processTress在state.ptreeNode这个节点上split
//					continueState->ptreeNode = res.first;
//					newState->ptreeNode = res.second;
//				}
//
//				zz++;
//			}
//
//			std::vector<std::vector<ExecutionInfo *> >::iterator ee1 =
//					ExeInfo.begin();
//			ee1 = ee1 + state.pathId;
//			std::vector<ExecutionInfo *>::iterator eeC = (*ee1).begin();
//			while (eeC != (*ee1).end())
//			{
//				if ((*eeC)->isDead == 1)
//				{
//					(*ee).push_back((*eeC));
//				}
//				eeC++;
//			}
//
//			state.globalId = 0;
//		} //ssg
		else {

			// FIXME: Find a way that we don't have this hidden dependency.
			assert(
					bi->getCondition() == bi->getOperand(0) && "Wrong operand index!");
			ref<Expr> cond = eval(ki, 0, state).value;
			Executor::StatePair branches = fork(state, cond, false);

			// NOTE: There is a hidden dependency here, markBranchVisited
			// requires that we still be in the context of the branch
			// instruction (it reuses its statistic id). Should be cleaned
			// up with convenient instruction specific data.
			if (statsTracker && state.stack.back().kf->trackCoverage)
				statsTracker->markBranchVisited(branches.first,
						branches.second);

			if (branches.first)
				transferToBasicBlock(bi->getSuccessor(0),
						bi->getParent(), *branches.first);
			if (branches.second)
				transferToBasicBlock(bi->getSuccessor(1),
						bi->getParent(), *branches.second);

			//ssg  新产生的state为新的路径，因此需要赋值新的路径号，但是线程号就不用改，因为还是一样的线程
			if (branches.first && branches.second) {

				///cc    	  branches.second->pathId = ExecutionState::createPathId;
				branches.second->setPathId(
						ExecutionState::createPathId);
				ExecutionState::createPathId++;

				//生成新的路径号，拷贝监控信息
				if (isMonitor == 1) {
					struct ExecutionImage *ei;
					ei = (struct ExecutionImage *) malloc(
							sizeof(struct ExecutionImage));
					memset(ei, 0, sizeof(struct ExecutionImage));
					ei->pathId = ExecutionState::createPathId - 1;
					ei->current = NULL;
					ei->pre = NULL;

					struct exePthreadInfo *tail = NULL;
					tail = (struct exePthreadInfo*) malloc(
							sizeof(struct exePthreadInfo));
					memset(tail, 0, sizeof(struct exePthreadInfo));
					tail->threadId = head->threadId;
					tail->type = head->type;
					tail->mutexAddr = head->mutexAddr;
					tail->newPthreadId = head->newPthreadId;
					tail->exec = head->exec;
					tail->disableFlag = head->disableFlag;
					tail->isDisable = head->isDisable;
					tail->lockOrder = head->lockOrder;
					tail->waitForExecutionStates.clear();
					tail->next = NULL;
					cloneExecutionInfo(tail);

					if (tail == NULL) {
						std::cout << "初始化出错\n";
						return;
					}
					ei->head = tail;

//				struct exePthreadInfo *tp = ei->head;
//				while (tp != NULL)
//				{
//					printf("线程:%d,类型:%d,互斥量:%d,标记:%d\n", tp->threadId, tp->type,
//							tp->mutexAddr, tp->disableFlag);
//					tp = tp->next;
//				}
					//新产生的路径的current的指向和产生新的path的原current指向保持一致
					ExecutionImage *tei = NULL;
					for (std::set<ExecutionImage*>::iterator it =
							executionImageList.begin(), ie =
							executionImageList.end(); it != ie;
							it++) {
						tei = *it;
						if (tei->pathId == state.pathId) {
							break;
						}
					}

					assert(tei != NULL);

					struct exePthreadInfo *p = tei->head;
					int coun = 0;
					int ai = 0;
//				if (tei->pre != NULL)
//				{
//					while (p < tei->pre)
//					{
//						coun++;
//						p = p->next;
//					}
//					ei->pre = ei->head;
//					for (ai = 0; ai < coun; ai++)
//					{
//						ei->pre = ei->pre->next;
//					}
//				}
					//找到原域中current的指向，用索引标记
					while (p != tei->current) {
						coun++;
						p = p->next;
					}

					ei->current = ei->head;
					for (ai = 0; ai < coun; ai++) {
						ei->current->exec = 1;
						ei->current->disableFlag = 0;
						ei->current->isDisable = 0;
						ei->current = ei->current->next;
					}
					executionImageList.insert(ei);
				}

				//hlm在新生成的state中加入新路径的执行信息
				if (branches.second->isMain == 0) {
					PthreadInfo *pthread = NULL;
					for (std::vector<PthreadInfo*>::iterator itp =
							threadList.begin(), iep =
							threadList.end(); itp != iep; itp++) {
						pthread = *itp;
						if (pthread->threadId
								== branches.second->pthreadId) {
							break;
						}
					}
					assert((pthread != NULL) && "线程不存在");
					pthread->isAlives.insert(
							pair<int, int>(
									branches.second->pathId,
									1));
//					std::cout << "线程" << branches.second->pthreadId << "路径"
//							<< branches.second->pathId << "创建成功\n";
				}
				//

				std::vector<ExecutionInfo *> pathExe;
				ExeInfo.push_back(pathExe);
				std::vector<std::vector<ExecutionInfo *> >::iterator ee =
						ExeInfo.begin();
				ee = ee + branches.second->pathId;
				(*ee).push_back(branches.second->exeInfo);

				//检查路径号与branches.first相同,但线程号不同的
				std::set<ExecutionState *>::iterator zz =
						states.begin();

				while (zz != states.end()) {
					if (branches.first->pathId == (*zz)->pathId
							&& branches.first->pthreadId
									!= (*zz)->pthreadId) {
						ExecutionState *continueState, *newState;
						++stats::forks; //stats是state的链表，forks是state的个数
						continueState = (*zz);
						newState = (*zz)->branch();
						///cc   newState->pathId = branches.second->pathId;
						newState->setPathId(
								branches.second->pathId);

						//hlm在其他线程state信息中加入新路径的执行信息
						if (newState->isMain == 0) {
							PthreadInfo *pthread = NULL;
							for (std::vector<PthreadInfo*>::iterator
									itp = threadList.begin(),
									iep = threadList.end();
									itp != iep; itp++) {
								pthread = *itp;
								if (pthread->threadId
										== newState->pthreadId) {
									break;
								}
							}
							assert((pthread != NULL) && "线程不存在");
							pthread->isAlives.insert(
									pair<int, int>(
											newState->pathId,
											1));
//							std::cout << "线程" << newState->pthreadId << "路径"
//									<< newState->pathId << "创建成功\n";
						}

						//判断被动生成的新state是否是处于等待状态，如果是处于等待状态，需要加入等待条件使其可以唤醒

						if (newState->isWait == 1) //处于等待状态，分析原因
								{

//							std::cout << "新产生的state处于等待状态\n";
							CallSite css(newState->prevPC->inst);
							Value *ffp = css.getCalledValue();
							Function *ff = getTargetFunction(ffp,
									*newState);
							assert(ff != NULL);
							KFunction *kff = new KFunction(ff,
									kmodule);
							assert(kff != NULL);
							KInstruction *kii = newState->prevPC;

							//如果是pthread_join使其等待
							if (!strcmp(ff->getName().data(),
									"pthread_join")) {

//								std::cout << "新产生的state因为pthread_join而处于等待中\n";
								assert(
										!newState->loadExpr.isNull());
								ConstantExpr *CE = dyn_cast<
										ConstantExpr>(
										newState->loadExpr);
								int threadIdentify =
										CE->getZExtValue();

								PthreadInfo *pthread = NULL;
								for (std::vector<PthreadInfo*>::iterator
										itp =
												threadList.begin(),
										iep =
												threadList.end();
										itp != iep; itp++) {
									pthread = *itp;
									if (pthread->threadIdentify
											== threadIdentify) {
										break;
									}
								}

								assert(
										(pthread != NULL) && "线程不存在");

								pthread->waitExitStates.push_back(
										newState);
							} else {
								newState->isWait = 0;
								newState->pc = newState->prevPC;
							}

						}

						//hlm

						addedStates.insert(newState);

						(*ee).push_back(newState->exeInfo);

						addConstraint(*continueState, cond);
						addConstraint(*newState,
								Expr::createIsZero(cond));

						(*zz)->ptreeNode->data = 0;
						std::pair<PTree::Node*, PTree::Node*> res =
								processTree->split(
										(*zz)->ptreeNode,
										continueState,
										newState); //processTress在state.ptreeNode这个节点上split
						continueState->ptreeNode = res.first;
						newState->ptreeNode = res.second;
					}

					zz++;
				}

				std::vector<std::vector<ExecutionInfo *> >::iterator ee1 =
						ExeInfo.begin();
				ee1 = ee1 + state.pathId;
				std::vector<ExecutionInfo *>::iterator eeC =
						(*ee1).begin();
				while (eeC != (*ee1).end()) {
					if ((*eeC)->isDead == 1) {
						(*ee).push_back((*eeC));
					}
					eeC++;
				}

			}
			//ssg
		}

		break;
	}
	case Instruction::Switch: {
		SwitchInst *si = cast<SwitchInst>(i);
		ref<Expr> cond = eval(ki, 0, state).value;
		BasicBlock *bb = si->getParent();

		cond = toUnique(state, cond);
		if (ConstantExpr * CE = dyn_cast<ConstantExpr>(cond)) {
			// Somewhat gross to create these all the time, but fine till we
			// switch to an internal rep.
			LLVM_TYPE_Q
			llvm::IntegerType *Ty = cast<IntegerType>(
					si->getCondition()->getType());
			ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
			unsigned index = si->findCaseValue(ci).getSuccessorIndex();
#else
			unsigned index = si->findCaseValue(ci);
#endif
			transferToBasicBlock(si->getSuccessor(index), si->getParent(),
					state);
		} else {
			std::map<BasicBlock*, ref<Expr> > targets;
			ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
			for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
					i != e; ++i)
			{
				ref < Expr > value = evalConstant(i.getCaseValue());
#else
			for (unsigned i = 1, cases = si->getNumCases(); i < cases;
					++i) {
				ref<Expr> value = evalConstant(si->getCaseValue(i));
#endif
				ref<Expr> match = EqExpr::create(cond, value);
				isDefault = AndExpr::create(isDefault,
						Expr::createIsZero(match));
				bool result;
				bool success = solver->mayBeTrue(state, match, result);
				assert(success && "FIXME: Unhandled solver failure");
				(void) success;
				if (result) {
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
					BasicBlock *caseSuccessor = i.getCaseSuccessor();
#else
					BasicBlock *caseSuccessor = si->getSuccessor(i);
#endif
					std::map<BasicBlock*, ref<Expr> >::iterator it =
							targets.insert(
									std::make_pair(
											caseSuccessor,
											ConstantExpr::alloc(
													0,
													Expr::Bool))).first;

					it->second = OrExpr::create(match, it->second);
				}
			}
			bool res;
			bool success = solver->mayBeTrue(state, isDefault, res);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			if (res)
				targets.insert(
						std::make_pair(si->getDefaultDest(),
								isDefault));

			std::vector<ref<Expr> > conditions;
			for (std::map<BasicBlock*, ref<Expr> >::iterator it =
					targets.begin(), ie = targets.end(); it != ie;
					++it)
				conditions.push_back(it->second);

			std::vector<ExecutionState*> branches;
			branch(state, conditions, branches);

			std::vector<ExecutionState*>::iterator bit = branches.begin();
			for (std::map<BasicBlock*, ref<Expr> >::iterator it =
					targets.begin(), ie = targets.end(); it != ie;
					++it) {
				ExecutionState *es = *bit;
				if (es)
					transferToBasicBlock(it->first, bb, *es);
				++bit;
			}
		}
		break;
	}
	case Instruction::Unreachable:
		// Note that this is not necessarily an internal bug, llvm will
		// generate unreachable instructions in cases where it knows the
		// program will crash. So it is effectively a SEGV or internal
		// error.
		terminateStateOnExecError(state,
				"reached \"unreachable\" instruction");
		break;

	case Instruction::Invoke:
	case Instruction::Call: {
		CallSite cs(i);

		unsigned numArgs = cs.arg_size();
		Value *fp = cs.getCalledValue();
		Function *f = getTargetFunction(fp, state);

//		std::cout << "线程" << state.pthreadId << "路径" << state.pathId << "调用的函数是"
//				<< f->getName().data() << std::endl;

		// Skip debug intrinsics, we can't evaluate their metadata arguments.
		if (f && isDebugIntrinsic(f, kmodule))
			break;

		if (isa<InlineAsm>(fp)) {
			terminateStateOnExecError(state,
					"inline assembly is unsupported");
			break;
		}
		// evaluate arguments
		std::vector<ref<Expr> > arguments;
		arguments.reserve(numArgs);

//在state中记录已经加的锁
		if (!strcmp(f->getName().data(), "pthread_mutex_lock")) {

			ref<Expr> base1 = eval(ki, 1, state).value;
			ObjectPair op;
			bool success;
			solver->setTimeout(stpTimeout);
			if (!state.addressSpace.resolveOne(state, solver, base1, op,
					success)) {
				base1 = toConstant(state, base1, "resolveOne failure");
				success = state.addressSpace.resolveOne(
						cast<ConstantExpr>(base1), op);
			}
			solver->setTimeout(0);

			if (success) {
				const MemoryObject *mo = op.first;
				state.mutex.push_back(mo->name);
			}
		} else if (!strcmp(f->getName().data(), "pthread_mutex_unlock")) {
			ref<Expr> base1 = eval(ki, 1, state).value;
			ObjectPair op;
			bool success;
			solver->setTimeout(stpTimeout);
			if (!state.addressSpace.resolveOne(state, solver, base1, op,
					success)) {
				base1 = toConstant(state, base1, "resolveOne failure");
				success = state.addressSpace.resolveOne(
						cast<ConstantExpr>(base1), op);
			}
			solver->setTimeout(0);

			if (success) {
				const MemoryObject *mo = op.first;
				std::vector<std::string>::iterator ai =
						state.mutex.begin();
				while (ai != state.mutex.end()) {
					if (mo->name == *ai) {

						state.mutex.erase(ai);
						ai = state.mutex.begin();
						continue;
					}
					++ai;
				}
			}
		}

		if (!strncmp(f->getName().data(), "pthread_",
				sizeof("pthread_") - 1)) {
			for (int j = 0; j < PTHREAD_HANDLE_NUMBER; j++) {
				if (!strcmp(f->getName().data(),
						pthreadHandles[j]->name)) {
					(this->*(pthreadHandles[j]->handle))(state, ki, i,
							numArgs, fp, f, arguments);
					break;
				}
			}
			break;
		} else if (!strcmp(f->getName().data(), "klee_roll_back")) {
			ref<Expr> base = eval(ki, 1, state).value;
			ConstantExpr *CE = dyn_cast<ConstantExpr>(
					eval(ki, 1, state).value);

			isRollBack = 1;

			int val = 0;
			if (CE != 0) {
				val = (int) CE->getZExtValue();

				//		std::cout << "val = " << val << std::endl;

				if (state.snapShotList.size() < val) {
					std::cout << "不能回滚\n";

				} else {
					//		std::cout<<"RollBack="<<RollBack<<std::endl;
					if (RollBack == 0) {
						if (val == 1) {
							//std::cout << "线程为" << state.pthreadId << "路径为"
							//		<< state.pathId << "结点为"
							//		<< state.ptreeNode->nodeId << std::endl;
							//std::cout << "state.snapShotList.size="
							//		<< state.snapShotList.size() << std::endl;
							ExecutionSnapShot *snapshot =
									state.snapShotList.back();

							std::cout << "程序进行回滚\n";
							rollBack(&state, *snapshot);
							RollBack = 1;
						}
					}
				}
			}

			break;
		}
		else if(!strcmp(f->getName().data(), "sleep"))
		{
			ConstantExpr *CE = dyn_cast<ConstantExpr>(
								eval(ki, 1, state).value);
			unsigned int val = 0;
			if (CE != 0)
			{
				val = (unsigned int) CE->getZExtValue();
				call_sleep(&state,val);
			}
			break;
		}
		else {

			//ssg

			for (unsigned j = 0; j < numArgs; ++j)
				arguments.push_back(eval(ki, j + 1, state).value);

			if (f) {
				const FunctionType *fType =
						dyn_cast<FunctionType>(
								cast<PointerType>(f->getType())->getElementType());
				const FunctionType *fpType =
						dyn_cast<FunctionType>(
								cast<PointerType>(fp->getType())->getElementType());

				// special case the call with a bitcast case
				if (fType != fpType) {
					assert(
							fType && fpType && "unable to get function type");

					// XXX check result coercion

					// XXX this really needs thought and validation
					unsigned i = 0;
					for (std::vector<ref<Expr> >::iterator ai =
							arguments.begin(), ie =
							arguments.end(); ai != ie; ++ai) {
						Expr::Width to, from = (*ai)->getWidth();

						if (i < fType->getNumParams()) {
							to = getWidthForLLVMType(
									fType->getParamType(i));

							if (from != to) {
								// XXX need to check other param attrs ?
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
								bool isSExt = cs.paramHasAttr(i + 1,
										llvm::Attributes::SExt);
#else
								bool isSExt =
										cs.paramHasAttr(
												i + 1,
												llvm::Attribute::SExt);
#endif
								if (isSExt) {
									arguments[i] =
											SExtExpr::create(
													arguments[i],
													to);
								} else {
									arguments[i] =
											ZExtExpr::create(
													arguments[i],
													to);
								}
							}
						}

						i++;
					}
				}

				executeCall(state, ki, f, arguments);
			} else {
				ref<Expr> v = eval(ki, 0, state).value;

				ExecutionState *free = &state;
				bool hasInvalid = false, first = true;

				/* XXX This is wasteful, no need to do a full evaluate since we
				 have already got a value. But in the end the caches should
				 handle it for us, albeit with some overhead. */
				do {
					ref<ConstantExpr> value;
					bool success = solver->getValue(*free, v, value);
					assert(
							success && "FIXME: Unhandled solver failure");
					(void) success;
					StatePair res = fork(*free,
							EqExpr::create(v, value), true);
					if (res.first) {
						uint64_t addr = value->getZExtValue();
						if (legalFunctions.count(addr)) {
							f = (Function*) addr;

							// Don't give warning on unique resolution
							if (res.second || !first)
								klee_warning_once(
										(void*) (unsigned long) addr,
										"resolved symbolic function pointer to: %s",
										f->getName().data());

							executeCall(*res.first, ki, f,
									arguments);
						} else {
							if (!hasInvalid) {
								terminateStateOnExecError(state,
										"invalid function pointer");
								hasInvalid = true;
							}
						}
					}

					first = false;
					free = res.second;
				} while (free);
			}
		}
		break;
	}
	case Instruction::PHI: {
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 0)
		ref < Expr > result = eval(ki, state.incomingBBIndex, state).value;
#else
		ref<Expr> result = eval(ki, state.incomingBBIndex * 2, state).value;
#endif
		bindLocal(ki, state, result);
		break;
	}

		// Special instructions
	case Instruction::Select: {
		SelectInst *SI = cast<SelectInst>(ki->inst);
		assert(
				SI->getCondition() == SI->getOperand(0) && "Wrong operand index!");
		ref<Expr> cond = eval(ki, 0, state).value;
		ref<Expr> tExpr = eval(ki, 1, state).value;
		ref<Expr> fExpr = eval(ki, 2, state).value;
		ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::VAArg:
		terminateStateOnExecError(state, "unexpected VAArg instruction");
		break;

		// Arithmetic / logical

	case Instruction::Add: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		bindLocal(ki, state, AddExpr::create(left, right));
		break;
	}

	case Instruction::Sub: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		bindLocal(ki, state, SubExpr::create(left, right));
		break;
	}

	case Instruction::Mul: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		bindLocal(ki, state, MulExpr::create(left, right));
		break;
	}

	case Instruction::UDiv: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = UDivExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::SDiv: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = SDivExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::URem: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = URemExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::SRem: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = SRemExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::And: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = AndExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::Or: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = OrExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::Xor: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = XorExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::Shl: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = ShlExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::LShr: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = LShrExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::AShr: {
		ref<Expr> left = eval(ki, 0, state).value;
		ref<Expr> right = eval(ki, 1, state).value;
		ref<Expr> result = AShrExpr::create(left, right);
		bindLocal(ki, state, result);
		break;
	}
		// Compare
	case Instruction::ICmp: {
		CmpInst *ci = cast<CmpInst>(i);
		ICmpInst *ii = cast<ICmpInst>(ci);

		switch (ii->getPredicate()) {
		case ICmpInst::ICMP_EQ: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;

			ConstantExpr *CE = dyn_cast<ConstantExpr>(right);
			//printf("icmp value:%d\n",CE->getZExtValue());

			//ssg 只考虑全局变量与一确定值比较
			if (state.globalId != 0 && CE != 0) {
				ExecutionMember global;
				uint64_t val = 0;
				val = CE->getZExtValue();
				global.type = 5;
				global.variableId = state.globalId;
				global.globalValue = val;
				global.constrainType = 1;
				state.exeInfo->exeInfo.push_back(global);
			}
			//state.globalId = 0;//注意，这里只是想先忽略全局变量判断的分支，实际不能这样
			//ssg
			ref<Expr> result = EqExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_NE: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = NeExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_UGT: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = UgtExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_UGE: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = UgeExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_ULT: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = UltExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_ULE: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = UleExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_SGT: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = SgtExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_SGE: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = SgeExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_SLT: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = SltExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		case ICmpInst::ICMP_SLE: {
			ref<Expr> left = eval(ki, 0, state).value;
			ref<Expr> right = eval(ki, 1, state).value;
			ref<Expr> result = SleExpr::create(left, right);
			bindLocal(ki, state, result);
			break;
		}

		default:
			terminateStateOnExecError(state, "invalid ICmp predicate");
		}
		break;
	}

		// Memory instructions...
#if LLVM_VERSION_CODE < LLVM_VERSION(2, 7)
		case Instruction::Malloc:
		case Instruction::Alloca:
		{
			AllocationInst *ai = cast<AllocationInst>(i);
#else
	case Instruction::Alloca: {
		AllocaInst *ai = cast<AllocaInst>(i);
#endif
		unsigned elementSize = kmodule->targetData->getTypeStoreSize(
				ai->getAllocatedType());
		ref<Expr> size = Expr::createPointer(elementSize);
		if (ai->isArrayAllocation()) {
			ref<Expr> count = eval(ki, 0, state).value;
			count = Expr::createZExtToPointerWidth(count);
			size = MulExpr::create(size, count);
		}
		bool isLocal = i->getOpcode() == Instruction::Alloca;
		executeAlloc(state, size, isLocal, ki);
		break;
	}
#if LLVM_VERSION_CODE < LLVM_VERSION(2, 7)
		case Instruction::Free:
		{
			executeFree(state, eval(ki, 0, state).value);
			break;
		}
#endif

	case Instruction::Load: {
		ref<Expr> base = eval(ki, 0, state).value;

//		//ssg  如果load了一个global的变量，则把该变量的id记录下来（state.globalId）
//		if (SimplifySymIndices)
//		{
//			if (!isa<ConstantExpr>(base))
//				base = state.constraints.simplifyExpr(base);
//		}
//
		ObjectPair op;
		bool success;
		solver->setTimeout(stpTimeout);
		if (!state.addressSpace.resolveOne(state, solver, base, op,
				success)) {
			base = toConstant(state, base, "resolveOne failure");
			success = state.addressSpace.resolveOne(
					cast<ConstantExpr>(base), op);
		}
		solver->setTimeout(0);

		if (success) {
			const MemoryObject *mo = op.first;

			if (mo->isGlobal || mo->localToGlobal != 0) {
//				state.globalId = mo->id;
//				std::cout << "在load指令中state.globalId=" << state.globalId
//						<< std::endl;
				//std::cout<<"!!!!!!!!!!!"<<state.pthreadId<<mo->name<<std::endl;
				//
				gloMutex med;
				med.name = mo->name;
				med.isRace = 0;

				std::vector<std::string>::iterator ai =
						state.mutex.begin();
				while (ai != state.mutex.end()) {
					med.mutex.push_back(*ai);
					++ai;
				}
				state.gm.push_back(med);
				//cc,print the global object message
				state.processInfo->callLoad(state, mo);
				//

			}

		}

//ssh
		//hlm
		state.loadExpr = base;
		//hlm
		executeMemoryOperation(state, false, base, 0, ki);
		break;
	}
	case Instruction::Store: {
		ref<Expr> base = eval(ki, 1, state).value;
		ref<Expr> value = eval(ki, 0, state).value;

		//ssg
		if (SimplifySymIndices) {
			if (!isa<ConstantExpr>(base))
				base = state.constraints.simplifyExpr(base);
		}

		ObjectPair op;
		bool success;
		solver->setTimeout(stpTimeout);
		if (!state.addressSpace.resolveOne(state, solver, base, op,
				success)) {
			base = toConstant(state, base, "resolveOne failure");
			success = state.addressSpace.resolveOne(
					cast<ConstantExpr>(base), op);
		}
		solver->setTimeout(0);

		if (success) {
			const MemoryObject *mo = op.first;

			if (mo->isGlobal || mo->localToGlobal != 0) {
//				state.globalId = mo->id;
//				std::cout << "在load指令中state.globalId=" << state.globalId
//						<< std::endl;
				//
				gloMutex med;
				med.name = mo->name;
				med.isRace = 0;

				std::vector<std::string>::iterator ai =
						state.mutex.begin();
				while (ai != state.mutex.end()) {
					med.mutex.push_back(*ai);
					++ai;
				}
				state.gm.push_back(med);
				//cc,print the global object message
				state.processInfo->callLoad(state, mo);
				//

			}

		}

		if (state.globalId == 0) { //记录全局变量被赋值,只记录确定性的赋值

			if (success) {
				const MemoryObject *mo = op.first;

				if (mo->isGlobal) { //判断是否为全局变量
					ConstantExpr *CE = dyn_cast<ConstantExpr>(
							eval(ki, 0, state).value);
					if (CE != 0) { //判断是否为确定性赋值
						uint64_t val = 0;
						val = CE->getZExtValue();

						ExecutionMember global;
						global.type = 3;
						global.variableId = mo->id;
						global.globalValue = val;
						state.exeInfo->exeInfo.push_back(global);
					}

					//记录下对其全局变量的访问操作
					GlobalAccessLog *gal;
					if (globalAccessList.size() == 0) {
						gal = new GlobalAccessLog();
						gal->globalId = mo->id;
						gal->flag = 1; //初次被访问
						gal->pthreadId = state.pthreadId;
						gal->pathId = state.pathId;
						for (aa = 0; aa < state.ownMutexList.size();
								aa++) {
							gal->mutexlist.push_back(
									state.ownMutexList[aa]);
						}
						globalAccessList.insert(gal);
					} else {
						int lag = 0;
						int lag1 = 0;
						for (std::set<GlobalAccessLog*>::iterator
								it = globalAccessList.begin(),
								ie = globalAccessList.end();
								it != ie; it++) {
							gal = *it;
							if (gal->globalId == mo->id) {
								lag = 1;
								break;
							}
						}

						int bb = 0;
						if (lag == 1) {
							for (bb = 0;
									bb
											< state.ownMutexList.size();
									bb++) {
								int tmp = state.ownMutexList[bb];
								for (aa = 0;
										aa
												< gal->mutexlist.size();
										aa++) {

									if ((gal->mutexlist[aa]
											== tmp)
											&& (gal->pthreadId
													!= state.pthreadId)) {
										lag1 = 1;
										break;
									}
								}
							}

							if (lag1 == 0) //不存在,则会发生数据竞争,将其置为0
									{
								gal->flag = 0;
							}
						} else {
							gal = new GlobalAccessLog();
							gal->globalId = mo->id;
							gal->flag = 1; //初次被访问
							gal->pthreadId = state.pthreadId;
							gal->pathId = state.pathId;
							for (aa = 0;
									aa
											< state.ownMutexList.size();
									aa++) {
								gal->mutexlist.push_back(
										state.ownMutexList[aa]);
							}
							globalAccessList.insert(gal);
						}
					}

//					std::cout << "-------------全局变量访问记录信息如下------" << std::endl;
//					for (std::set<GlobalAccessLog*>::iterator it =
//							globalAccessList.begin(), ie =
//							globalAccessList.end(); it != ie; it++)
//					{
//						GlobalAccessLog *gal = *it;
//						std::cout << "globalId:" << gal->globalId
//								<< ",pthreadId:" << gal->pthreadId << ",pathId:"
//								<< gal->pathId << ",flag:" << gal->flag
//								<< std::endl;
//						std::cout<<"此时全局变量"<<gal->globalId<<"拥有的锁为:";
//						for(aa=0;aa<gal->mutexlist.size();aa++)
//						{
//							std::cout<<gal->mutexlist[aa]<<",";
//						}
//						std::cout<<std::endl;
//					}
//					std::cout << "-------------全局变量访问记录信息结束------" << std::endl;

					//hlm只更新同一域里面的全局变量
					for (std::set<ExecutionState*>::iterator it =
							states.begin(), ie = states.end();
							it != ie; ++it) {
						ExecutionState *es = *it;
						if ((es->pathId == state.pathId)) {
							executeMemoryOperation(*es, true,
									base, value, 0);
						}
					}
					//hlm
				} else {
					mo->localToGlobal = 0;
				}
				///cc,print the global object message
				if (mo->isGlobal || !(mo->isLocal)) {
					state.processInfo->callStore(state, mo);
				}
			}
		} else { //记录全局变量赋值给其他变量
			if (success) {
				const MemoryObject *mo = op.first;

				mo->localToGlobal = state.globalId;

				ExecutionMember global;
				global.type = 4;
				global.variableId = mo->id; //其他变量id
				global.globalId = state.globalId; //全局变量id
				state.globalId = 0;
				state.exeInfo->exeInfo.push_back(global);

				///cc,print the global object message
				if (mo->isGlobal || !(mo->isLocal)) {
					state.processInfo->callStore(state, mo);
				}
			}
		}

		//hlm
		if (value.isNull()) {
			ref<Expr> res = ConstantExpr::create(0, Expr::Int32);
			value = res;
		}

		assert(value.get() != NULL);

		//hlm
		executeMemoryOperation(state, true, base, value, 0);

		break;
	}

	case Instruction::GetElementPtr: {
		KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
		ref<Expr> base = eval(ki, 0, state).value;

		for (std::vector<std::pair<unsigned, uint64_t> >::iterator it =
				kgepi->indices.begin(), ie = kgepi->indices.end();
				it != ie; ++it) {
			uint64_t elementSize = it->second;
			ref<Expr> index = eval(ki, it->first, state).value;
			base = AddExpr::create(base,
					MulExpr::create(
							Expr::createSExtToPointerWidth(index),
							Expr::createPointer(elementSize)));
		}
		if (kgepi->offset)
			base = AddExpr::create(base,
					Expr::createPointer(kgepi->offset));
		bindLocal(ki, state, base);
		break;
	}

		// Conversion
	case Instruction::Trunc: {
		CastInst *ci = cast<CastInst>(i);
		ref<Expr> result = ExtractExpr::create(eval(ki, 0, state).value, 0,
				getWidthForLLVMType(ci->getType()));
		bindLocal(ki, state, result);
		break;
	}
	case Instruction::ZExt: {
		CastInst *ci = cast<CastInst>(i);
		ref<Expr> result = ZExtExpr::create(eval(ki, 0, state).value,
				getWidthForLLVMType(ci->getType()));
		bindLocal(ki, state, result);
		break;
	}
	case Instruction::SExt: {
		CastInst *ci = cast<CastInst>(i);
		ref<Expr> result = SExtExpr::create(eval(ki, 0, state).value,
				getWidthForLLVMType(ci->getType()));
		bindLocal(ki, state, result);
		break;
	}

	case Instruction::IntToPtr: {
		CastInst *ci = cast<CastInst>(i);
		Expr::Width pType = getWidthForLLVMType(ci->getType());
		ref<Expr> arg = eval(ki, 0, state).value;
		bindLocal(ki, state, ZExtExpr::create(arg, pType));
		break;
	}
	case Instruction::PtrToInt: {
		CastInst *ci = cast<CastInst>(i);
		Expr::Width iType = getWidthForLLVMType(ci->getType());
		ref<Expr> arg = eval(ki, 0, state).value;
		bindLocal(ki, state, ZExtExpr::create(arg, iType));
		break;
	}

	case Instruction::BitCast: {
		ref<Expr> result = eval(ki, 0, state).value;
		bindLocal(ki, state, result);
		break;
	}

		// Floating point instructions

	case Instruction::FAdd: {
		ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		ref<ConstantExpr> right = toConstant(state,
				eval(ki, 1, state).value, "floating point");
		if (!fpWidthToSemantics(left->getWidth())
				|| !fpWidthToSemantics(right->getWidth()))
			return terminateStateOnExecError(state,
					"Unsupported FAdd operation");

		llvm::APFloat Res(left->getAPValue());
		Res.add(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
		bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
		break;
	}

	case Instruction::FSub: {
		ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		ref<ConstantExpr> right = toConstant(state,
				eval(ki, 1, state).value, "floating point");
		if (!fpWidthToSemantics(left->getWidth())
				|| !fpWidthToSemantics(right->getWidth()))
			return terminateStateOnExecError(state,
					"Unsupported FSub operation");

		llvm::APFloat Res(left->getAPValue());
		Res.subtract(APFloat(right->getAPValue()),
				APFloat::rmNearestTiesToEven);
		bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
		break;
	}

	case Instruction::FMul: {
		ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		ref<ConstantExpr> right = toConstant(state,
				eval(ki, 1, state).value, "floating point");
		if (!fpWidthToSemantics(left->getWidth())
				|| !fpWidthToSemantics(right->getWidth()))
			return terminateStateOnExecError(state,
					"Unsupported FMul operation");

		llvm::APFloat Res(left->getAPValue());
		Res.multiply(APFloat(right->getAPValue()),
				APFloat::rmNearestTiesToEven);
		bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
		break;
	}

	case Instruction::FDiv: {
		ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		ref<ConstantExpr> right = toConstant(state,
				eval(ki, 1, state).value, "floating point");
		if (!fpWidthToSemantics(left->getWidth())
				|| !fpWidthToSemantics(right->getWidth()))
			return terminateStateOnExecError(state,
					"Unsupported FDiv operation");

		llvm::APFloat Res(left->getAPValue());
		Res.divide(APFloat(right->getAPValue()),
				APFloat::rmNearestTiesToEven);
		bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
		break;
	}

	case Instruction::FRem: {
		ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		ref<ConstantExpr> right = toConstant(state,
				eval(ki, 1, state).value, "floating point");
		if (!fpWidthToSemantics(left->getWidth())
				|| !fpWidthToSemantics(right->getWidth()))
			return terminateStateOnExecError(state,
					"Unsupported FRem operation");

		llvm::APFloat Res(left->getAPValue());
		Res.mod(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
		bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
		break;
	}

	case Instruction::FPTrunc: {
		FPTruncInst *fi = cast<FPTruncInst>(i);
		Expr::Width resultType = getWidthForLLVMType(fi->getType());
		ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		if (!fpWidthToSemantics(arg->getWidth())
				|| resultType > arg->getWidth())
			return terminateStateOnExecError(state,
					"Unsupported FPTrunc operation");

		llvm::APFloat Res(arg->getAPValue());
		bool losesInfo = false;
		Res.convert(*fpWidthToSemantics(resultType),
				llvm::APFloat::rmNearestTiesToEven, &losesInfo);
		bindLocal(ki, state, ConstantExpr::alloc(Res));
		break;
	}

	case Instruction::FPExt: {
		FPExtInst *fi = cast<FPExtInst>(i);
		Expr::Width resultType = getWidthForLLVMType(fi->getType());
		ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		if (!fpWidthToSemantics(arg->getWidth())
				|| arg->getWidth() > resultType)
			return terminateStateOnExecError(state,
					"Unsupported FPExt operation");

		llvm::APFloat Res(arg->getAPValue());
		bool losesInfo = false;
		Res.convert(*fpWidthToSemantics(resultType),
				llvm::APFloat::rmNearestTiesToEven, &losesInfo);
		bindLocal(ki, state, ConstantExpr::alloc(Res));
		break;
	}

	case Instruction::FPToUI: {
		FPToUIInst *fi = cast<FPToUIInst>(i);
		Expr::Width resultType = getWidthForLLVMType(fi->getType());
		ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
			return terminateStateOnExecError(state,
					"Unsupported FPToUI operation");

		llvm::APFloat Arg(arg->getAPValue());
		uint64_t value = 0;
		bool isExact = true;
		Arg.convertToInteger(&value, resultType, false,
				llvm::APFloat::rmTowardZero, &isExact);
		bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
		break;
	}

	case Instruction::FPToSI: {
		FPToSIInst *fi = cast<FPToSIInst>(i);
		Expr::Width resultType = getWidthForLLVMType(fi->getType());
		ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
			return terminateStateOnExecError(state,
					"Unsupported FPToSI operation");

		llvm::APFloat Arg(arg->getAPValue());
		uint64_t value = 0;
		bool isExact = true;
		Arg.convertToInteger(&value, resultType, true,
				llvm::APFloat::rmTowardZero, &isExact);
		bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
		break;
	}

	case Instruction::UIToFP: {
		UIToFPInst *fi = cast<UIToFPInst>(i);
		Expr::Width resultType = getWidthForLLVMType(fi->getType());
		ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		const llvm::fltSemantics *semantics = fpWidthToSemantics(
				resultType);
		if (!semantics)
			return terminateStateOnExecError(state,
					"Unsupported UIToFP operation");
		llvm::APFloat f(*semantics, 0);
		f.convertFromAPInt(arg->getAPValue(), false,
				llvm::APFloat::rmNearestTiesToEven);

		bindLocal(ki, state, ConstantExpr::alloc(f));
		break;
	}

	case Instruction::SIToFP: {
		SIToFPInst *fi = cast<SIToFPInst>(i);
		Expr::Width resultType = getWidthForLLVMType(fi->getType());
		ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		const llvm::fltSemantics *semantics = fpWidthToSemantics(
				resultType);
		if (!semantics)
			return terminateStateOnExecError(state,
					"Unsupported SIToFP operation");
		llvm::APFloat f(*semantics, 0);
		f.convertFromAPInt(arg->getAPValue(), true,
				llvm::APFloat::rmNearestTiesToEven);

		bindLocal(ki, state, ConstantExpr::alloc(f));
		break;
	}

	case Instruction::FCmp: {
		FCmpInst *fi = cast<FCmpInst>(i);
		ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
				"floating point");
		ref<ConstantExpr> right = toConstant(state,
				eval(ki, 1, state).value, "floating point");
		if (!fpWidthToSemantics(left->getWidth())
				|| !fpWidthToSemantics(right->getWidth()))
			return terminateStateOnExecError(state,
					"Unsupported FCmp operation");

		APFloat LHS(left->getAPValue());
		APFloat RHS(right->getAPValue());
		APFloat::cmpResult CmpRes = LHS.compare(RHS);

		bool Result = false;
		switch (fi->getPredicate()) {
		// Predicates which only care about whether or not the operands are NaNs.
		case FCmpInst::FCMP_ORD:
			Result = CmpRes != APFloat::cmpUnordered;
			break;

		case FCmpInst::FCMP_UNO:
			Result = CmpRes == APFloat::cmpUnordered;
			break;

			// Ordered comparisons return false if either operand is NaN.  Unordered
			// comparisons return true if either operand is NaN.
		case FCmpInst::FCMP_UEQ:
			if (CmpRes == APFloat::cmpUnordered) {
				Result = true;
				break;
			}
		case FCmpInst::FCMP_OEQ:
			Result = CmpRes == APFloat::cmpEqual;
			break;

		case FCmpInst::FCMP_UGT:
			if (CmpRes == APFloat::cmpUnordered) {
				Result = true;
				break;
			}
		case FCmpInst::FCMP_OGT:
			Result = CmpRes == APFloat::cmpGreaterThan;
			break;

		case FCmpInst::FCMP_UGE:
			if (CmpRes == APFloat::cmpUnordered) {
				Result = true;
				break;
			}
		case FCmpInst::FCMP_OGE:
			Result = CmpRes == APFloat::cmpGreaterThan
					|| CmpRes == APFloat::cmpEqual;
			break;

		case FCmpInst::FCMP_ULT:
			if (CmpRes == APFloat::cmpUnordered) {
				Result = true;
				break;
			}
		case FCmpInst::FCMP_OLT:
			Result = CmpRes == APFloat::cmpLessThan;
			break;

		case FCmpInst::FCMP_ULE:
			if (CmpRes == APFloat::cmpUnordered) {
				Result = true;
				break;
			}
		case FCmpInst::FCMP_OLE:
			Result = CmpRes == APFloat::cmpLessThan
					|| CmpRes == APFloat::cmpEqual;
			break;

		case FCmpInst::FCMP_UNE:
			Result = CmpRes == APFloat::cmpUnordered
					|| CmpRes != APFloat::cmpEqual;
			break;
		case FCmpInst::FCMP_ONE:
			Result = CmpRes != APFloat::cmpUnordered
					&& CmpRes != APFloat::cmpEqual;
			break;

		default:
			assert(0 && "Invalid FCMP predicate!");
		case FCmpInst::FCMP_FALSE:
			Result = false;
			break;
		case FCmpInst::FCMP_TRUE:
			Result = true;
			break;
		}

		bindLocal(ki, state, ConstantExpr::alloc(Result, Expr::Bool));
		break;
	}
	case Instruction::InsertValue: {
		KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

		ref<Expr> agg = eval(ki, 0, state).value;
		ref<Expr> val = eval(ki, 1, state).value;

		ref<Expr> l = NULL, r = NULL;
		unsigned lOffset = kgepi->offset * 8, rOffset = kgepi->offset * 8
				+ val->getWidth();

		if (lOffset > 0)
			l = ExtractExpr::create(agg, 0, lOffset);
		if (rOffset < agg->getWidth())
			r = ExtractExpr::create(agg, rOffset,
					agg->getWidth() - rOffset);

		ref<Expr> result;
		if (!l.isNull() && !r.isNull())
			result = ConcatExpr::create(r, ConcatExpr::create(val, l));
		else if (!l.isNull())
			result = ConcatExpr::create(val, l);
		else if (!r.isNull())
			result = ConcatExpr::create(r, val);
		else
			result = val;

		bindLocal(ki, state, result);
		break;
	}
	case Instruction::ExtractValue: {
		KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

		ref<Expr> agg = eval(ki, 0, state).value;

		ref<Expr> result = ExtractExpr::create(agg, kgepi->offset * 8,
				getWidthForLLVMType(i->getType()));

		bindLocal(ki, state, result);
		break;
	}

		// Other instructions...
		// Unhandled
	case Instruction::ExtractElement:
	case Instruction::InsertElement:
	case Instruction::ShuffleVector:
		terminateStateOnError(state, "XXX vector instructions unhandled",
				"xxx.err");
		break;

	default:
		terminateStateOnExecError(state, "illegal instruction");
		break;
	}
}

void Executor::updateStates(ExecutionState *current) {
	if (searcher) {
		searcher->update(current, addedStates, removedStates);
	}

	states.insert(addedStates.begin(), addedStates.end());
	addedStates.clear();

	for (std::set<ExecutionState*>::iterator it = removedStates.begin(), ie =
			removedStates.end(); it != ie; ++it) {
		ExecutionState *es = *it;
		std::set<ExecutionState*>::iterator it2 = states.find(es);
		assert(it2 != states.end());
		states.erase(it2);
		std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it3 =
				seedMap.find(es);
		if (it3 != seedMap.end())
			seedMap.erase(it3);
		if (isRollBack == 0) {
			processTree->remove(es->ptreeNode);
		} else {
			processTree->delNode(es->ptreeNode);
		}
		delete es;
	}
	removedStates.clear();

	if (isRollBack == 1) {
		for (std::set<PTree::Node*>::iterator it = deletedNodes.begin(),
				ie = deletedNodes.end(); it != ie; it++) {
			processTree->delNode(*it);
		}
		deletedNodes.clear();
		isRollBack = 0;
	}
}

template<typename TypeIt>
void Executor::computeOffsets(KGEPInstruction *kgepi, TypeIt ib, TypeIt ie) {
	ref<ConstantExpr> constantOffset = ConstantExpr::alloc(0,
			Context::get().getPointerWidth());
	uint64_t index = 1;
	for (TypeIt ii = ib; ii != ie; ++ii) {
		if (LLVM_TYPE_Q StructType *st = dyn_cast<StructType>(*ii)) {
			const StructLayout *sl = kmodule->targetData->getStructLayout(
					st);
			const ConstantInt *ci = cast<ConstantInt>(ii.getOperand());
			uint64_t addend = sl->getElementOffset(
					(unsigned) ci->getZExtValue());
			constantOffset = constantOffset->Add(
					ConstantExpr::alloc(addend,
							Context::get().getPointerWidth()));
		} else {
			const SequentialType *set = cast<SequentialType>(*ii);
			uint64_t elementSize = kmodule->targetData->getTypeStoreSize(
					set->getElementType());
			Value *operand = ii.getOperand();
			if (Constant * c = dyn_cast<Constant>(operand)) {
				ref<ConstantExpr> index = evalConstant(c)->SExt(
						Context::get().getPointerWidth());
				ref<ConstantExpr> addend =
						index->Mul(
								ConstantExpr::alloc(elementSize,
										Context::get().getPointerWidth()));
				constantOffset = constantOffset->Add(addend);
			} else {
				kgepi->indices.push_back(
						std::make_pair(index, elementSize));
			}
		}
		index++;
	}
	kgepi->offset = constantOffset->getZExtValue();
}

void Executor::bindInstructionConstants(KInstruction *KI) {
	KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(KI);

	if (GetElementPtrInst * gepi = dyn_cast<GetElementPtrInst>(KI->inst)) {
		computeOffsets(kgepi, gep_type_begin(gepi), gep_type_end(gepi));
	} else if (InsertValueInst * ivi = dyn_cast<InsertValueInst>(KI->inst)) {
		computeOffsets(kgepi, iv_type_begin(ivi), iv_type_end(ivi));
		assert(
				kgepi->indices.empty() && "InsertValue constant offset expected");
	} else if (ExtractValueInst * evi = dyn_cast<ExtractValueInst>(
			KI->inst)) {
		computeOffsets(kgepi, ev_type_begin(evi), ev_type_end(evi));
		assert(
				kgepi->indices.empty() && "ExtractValue constant offset expected");
	}
}

void Executor::bindModuleConstants() {
	for (std::vector<KFunction*>::iterator it = kmodule->functions.begin(),
			ie = kmodule->functions.end(); it != ie; ++it) {
		KFunction *kf = *it;
		for (unsigned i = 0; i < kf->numInstructions; ++i)
			bindInstructionConstants(kf->instructions[i]);
	}

	kmodule->constantTable = new Cell[kmodule->constants.size()];
	for (unsigned i = 0; i < kmodule->constants.size(); ++i) {
		Cell &c = kmodule->constantTable[i];
		c.value = evalConstant(kmodule->constants[i]);
	}
}

void Executor::checkRace() {
	std::set<ExecutionState*>::iterator iState = states.begin();
	std::set<ExecutionState*>::iterator medState = states.begin();
	int stateNum = 0;
	int medNum = 0;
	int isRace = 0;
	int cixu = 0;
	std::vector<gloMutex>::iterator iGlo;
	std::vector<gloMutex>::iterator medGlo;
	std::vector<std::string>::iterator iMutex;
	std::vector<std::string>::iterator mediMutex;
	std::vector<std::string>::iterator medMutex;
	while (stateNum < states.size()) { //遍历线程
		iGlo = (*iState)->gm.begin();
		while (iGlo < (*iState)->gm.end()) { //遍历线程的全局变量
			iMutex = (*iGlo).mutex.begin();
			medState = iState; //遍历其余没有比较过的线程
			++medState;
			medNum = stateNum + 1;
			while (medNum < states.size()) {
				medGlo = (*medState)->gm.begin();
				while (medGlo < (*medState)->gm.end()) { //遍历线程的全局变量
					isRace = 1;
					if (medGlo->name != iGlo->name) {
						++medGlo;
						continue;
					}
					medMutex = (*medGlo).mutex.begin();
					while (medMutex < (*medGlo).mutex.end()) { //全局变量的锁相比较，有相同的则break
						mediMutex = iMutex;
						while (mediMutex < (*iGlo).mutex.end()) {
							if (*mediMutex == *medMutex) { //有一个锁相同
								isRace = 0;
								break;
							}
							++mediMutex;
						}
						if (isRace == 0) {
							break;
						}
						++medMutex;
					}

					if (isRace == 1) { //发生了数据竞争

						//std::cout<<"------------data race------------"<<std::endl;
						//std::cout<<"thread id: "<<(*iState)->pthreadId<<" access global variable: "<<(iGlo)->name<<std::endl;
						//std::cout<<"and the locks are:";
						mediMutex = iMutex;
						while (mediMutex < (*iGlo).mutex.end()) {
							std::cout << *mediMutex << std::endl;
							++mediMutex;
						}
						//std::cout<<"thread id: "<<(*medState)->pthreadId<<" access global "<<(medGlo)->name<<std::endl;
						//std::cout<<"and the locks are:";
						mediMutex = (*medGlo).mutex.begin();
						while (mediMutex < (*medGlo).mutex.end()) {
							//	std::cout<<*mediMutex<<std::endl;
							break;//注意这里有问题，因为记录到多个相同的锁，估计是控制线程执行时，收到同步操作的影像
							//当不是当前加锁操作执行的时候，会多次执行调用函数pthread_mutex_lock。这里为了
							++mediMutex;
						}
						//std::cout<<"---------------------------------"<<std::endl;
					}

					++medGlo;
				}
				++medState;
				++medNum;
			}

//			while(iMutex < (*iGlo).mutex.end()){//遍历全局变量的锁
			//			std::cout<<*iMutex<<std::endl;
			//		++iMutex;
			//}
			++iGlo;
		}

		++iState;
		++stateNum;
	}

}

void Executor::run(ExecutionState &initialState) {
	bindModuleConstants();

// Delay init till now so that ticks don't accrue during
// optimization and such.
	initTimers();
	//--WXF--------replay------------
	ExecutionState* lastWrongState = NULL;
	//--------------------------------
	ExecutionState::createPthreadId = 0;

	states.insert(&initialState);

	if (isMonitor == 0) {
		initialState.pthreadId = ExecutionState::createPthreadId;
		ExecutionState::createPthreadId++;
	} else {

		if (head == NULL) {
			std::cout << "head初始化错误\n";
		} else {
			//std::cout << head->threadId << std::endl;
			initialState.pthreadId = head->threadId;
		}
	}
///cc  initialState.pathId = ExecutionState::createPathId;
	initialState.setPathId(ExecutionState::createPathId);
	ExecutionState::createPathId++;
//	initialState.pathId = ExecutionState::createPathId;
//	ExecutionState::createPathId++;

//hlm
//每个路径都有一个监控信息的拷贝
	if (isMonitor == 1) {
		struct ExecutionImage *ei;
		ei = (struct ExecutionImage *) malloc(
				sizeof(struct ExecutionImage));
		memset(ei, 0, sizeof(struct ExecutionImage));
		ei->pathId = 0;
		ei->current = NULL;
		ei->pre = NULL;

		struct exePthreadInfo *tail = NULL;
		tail = (struct exePthreadInfo*) malloc(
				sizeof(struct exePthreadInfo));
		memset(tail, 0, sizeof(struct exePthreadInfo));
		tail->threadId = head->threadId;
		tail->type = head->type;
		tail->mutexAddr = head->mutexAddr;
		tail->newPthreadId = head->newPthreadId;
		tail->exec = head->exec;
		tail->disableFlag = head->disableFlag;
		tail->isDisable = head->isDisable;
		tail->waitForExecutionStates.clear();
		tail->next = NULL;
		tail->lockOrder = head->lockOrder;
		cloneExecutionInfo(tail);

		if (tail == NULL) {
			std::cout << "初始化出错\n";
			return;
		}

//	struct exePthreadInfo *p = tail;
//	while (p != NULL)
//	{
//		printf("线程:%d,类型:%d,互斥量:%d,标记:%d\n", p->threadId, p->type, p->mutexAddr,
//				p->disableFlag);
//		p = p->next;
//	}
		ei->head = tail;
		ei->current = ei->head;
		executionImageList.insert(ei);
		//hlm
	}

	initialState.exeInfo = new ExecutionInfo();

	std::vector<ExecutionInfo *> pathExe;
	ExeInfo.push_back(pathExe);
	std::vector<std::vector<ExecutionInfo *> >::iterator ee = ExeInfo.begin();
	(*ee).push_back(initialState.exeInfo);

	if (usingSeeds) {
		std::vector<SeedInfo> &v = seedMap[&initialState];

		for (std::vector<KTest*>::const_iterator it = usingSeeds->begin(),
				ie = usingSeeds->end(); it != ie; ++it)
			v.push_back(SeedInfo(*it));

		int lastNumSeeds = usingSeeds->size() + 10;
		double lastTime, startTime = lastTime = util::getWallTime();
		ExecutionState *lastState = 0;
		while (!seedMap.empty()) {
			if (haltExecution)
				goto dump;

			std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it =
					seedMap.upper_bound(lastState);
			if (it == seedMap.end())
				it = seedMap.begin();
			lastState = it->first;
			unsigned numSeeds = it->second.size();
			ExecutionState &state = *lastState;
			KInstruction *ki = state.pc;
			stepInstruction(state);

			executeInstruction(state, ki);
			processTimers(&state, MaxInstructionTime * numSeeds);
			updateStates(&state);

			if ((stats::instructions % 1000) == 0) {
				int numSeeds = 0, numStates = 0;
				for (std::map<ExecutionState*, std::vector<SeedInfo> >::iterator
						it = seedMap.begin(), ie = seedMap.end();
						it != ie; ++it) {
					numSeeds += it->second.size();
					numStates++;
				}
				double time = util::getWallTime();
				if (SeedTime > 0. && time > startTime + SeedTime) {
					klee_warning(
							"seed time expired, %d seeds remain over %d states",
							numSeeds, numStates);
					break;
				} else if (numSeeds <= lastNumSeeds - 10
						|| time >= lastTime + 10) {
					lastTime = time;
					lastNumSeeds = numSeeds;
					klee_message("%d seeds remaining over: %d states",
							numSeeds, numStates);
				}
			}
		}

		klee_message("seeding done (%d states remain)",
				(int) states.size());

		// XXX total hack, just because I like non uniform better but want
		// seed results to be equally weighted.
		for (std::set<ExecutionState*>::iterator it = states.begin(), ie =
				states.end(); it != ie; ++it) {
			(*it)->weight = 1.;
		}

		if (OnlySeed)
			goto dump;
	}

	searcher = constructUserSearcher(*this);

	searcher->update(0, states, std::set<ExecutionState*>());


	while (!states.empty() && !haltExecution) {

		if(!updateSleepState())
			continue;
		ExecutionState &state = searcher->selectState();
		//------------------------重放控制-----------------------------
		/*
		重放的时候可以在此处进行判断state是否是要执行的state,
		若不是，设置state的canBeChosed标识，表示该state暂时不可选
		然后再次调用selectedState()，在所有searcher子类中的selectState()已经修改
		首先判断是不是读写全局变量（读写判断，全局变量判断）
		然后事件号增加
		根据线程号和事件号来判断是否执行该状态。
		*/
		if(replayOrNot)
		{
			if(lastWrongState != NULL)
			{
				lastWrongState->canBeChose = true;
				lastWrongState = NULL;
			}
			KInstruction *ki = state.pc;
			if(checkInstructionForReplay(state, ki))
			{

				bool rightState = replay->IsRightState(state.pthreadId,
						replay->pthread_event[state.pthreadId]);
				printf("pthreadId:%d  , event: %d , line:%d\n",state.pthreadId,
						replay->pthread_event[state.pthreadId],
						(*(ki->inst)).getDebugLoc().getLine());
				if(!rightState)
				{
					lastWrongState = &state;
					lastWrongState->canBeChose = false;
					continue;
				}
				else
					replay->update_record(state.pthreadId,
						replay->pthread_event[state.pthreadId]);
				replay->pthread_event[state.pthreadId]++;
			}
		}
		//----------------------------------------------------

		if (state.isWait == 0) {
			KInstruction *ki = state.pc;

			//llvm::outs() << *(ki->inst) << '\n';

			stepInstruction(state);
			//wxf
			//std::cout<<state.pthreadId<<std::endl;
			//上一步PC++；checkSiamese()检查全局变量，设置连同标志，调用监视函数
			checkSiamese(state, ki);
			//wxf
			executeInstruction(state, ki);


			//hlm
//			BasicBlock *parent = ki->inst->getParent();
//			Function *ff = parent->getParent();
//			std::string functionName = ff->getNameStr();
//			std::string basicBlockName = parent->getNameStr();
//
//			for (unsigned aa = 0; aa < targetobjects.size(); aa++)
//			{
//				TargetObject tarobj = targetobjects[aa];
//				int flag1 = functionName.compare(tarobj.functionName);
//				int flag2 = basicBlockName.compare(tarobj.basicBlockName);
//				if (!flag1 && !flag2)
//				{
//					std::cout << "函数名:" << functionName << ",基本块名:"
//							<< basicBlockName << std::endl;
//					std::cout << "线程" << state.pthreadId << ",路径"
//							<< state.pathId;
//					std::cout << ",进去目标块：" << state.countOffset << std::endl;
//					state.countOffset++;
//					if (state.countOffset == tarobj.offset)
//					{
//						std::cout << "state.countOffset=" << state.countOffset
//								<< std::endl;
//						std::cout << "程序到达出错位置" << std::endl;
//
//						state.isWait = 1;
//					}
//				}
//			}
			//hlm

			processTimers(&state, MaxInstructionTime);

			if (MaxMemory) {
				if ((stats::instructions & 0xFFFF) == 0) {
					// We need to avoid calling GetMallocUsage() often because it
					// is O(elts on freelist). This is really bad since we start
					// to pummel the freelist once we hit the memory cap.
					unsigned mbs = sys::Process::GetTotalMemoryUsage()
							>> 20;

					if (mbs > MaxMemory) {
						if (mbs > MaxMemory + 100) {
							// just guess at how many to kill
							unsigned numStates = states.size();
							unsigned toKill =
									std::max(1U,
											numStates
													- numStates
															* MaxMemory
															/ mbs);

							if (MaxMemoryInhibit)
								klee_warning(
										"killing %d states (over memory cap)",
										toKill);

							std::vector<ExecutionState*> arr(
									states.begin(),
									states.end());
							for (unsigned i = 0, N = arr.size();
									N && i < toKill;
									++i, --N) {
								unsigned idx = rand() % N;

								// Make two pulls to try and not hit a state that
								// covered new code.
								if (arr[idx]->coveredNew)
									idx = rand() % N;

								std::swap(arr[idx], arr[N - 1]);
								terminateStateEarly(*arr[N - 1],
										"Memory limit exceeded.");
							}
						}
						atMemoryLimit = true;
					} else {
						atMemoryLimit = false;
					}
				}
			}
			updateStates(&state);
		}
//		std::cout << "states.size()=" << states.size() << std::endl;

//		int flag1 =0;
//		for (std::set<ExecutionState*>::iterator it = states.begin(), ie =
//				states.end(); it != ie; ++it)
//		{
//			ExecutionState *st = *it;
//			if (st->isWait ==0)
//			{
//				flag1 = 1;
//				break;
//			}
//		}
//
//		if ((flag1 == 0) && (states.size() > 0))
//		{
//			std::cout << "出现死锁，程序终止\n";
//			return;
//		}

//		printf("flag1=%d\n",flag1);
//		if ((flag1 == 0) && (states.size() > 0))
//		{
//			std::cout << "出现死锁，程序终止\n";
//			return;
//		}

		//找到是那一条路径下的执行信息
		if (isMonitor == 1) {
			int pathId = state.pathId;
			struct ExecutionImage *ei = NULL;
			for (std::set<ExecutionImage*>::iterator it =
					executionImageList.begin(), ie =
					executionImageList.end(); it != ie; it++) {
				ei = *it;
				if (ei->pathId == pathId) {
					break;
				}
			}
			assert((ei != NULL) && ("路径拷贝监控信息出错！"));

			int flag1 = 0;
			std::set<ExecutionState*>::iterator it = states.begin();
			std::set<ExecutionState*>::iterator ie = states.end();
			ExecutionState *st = NULL;
			for (; it != ie; it++) {
				st = *it;
				if (st->isWait == 0) {
					flag1 = 1;
					break;
				}
			}

			if (flag1 == 0) {
				struct exePthreadInfo *p = ei->head;

				while (p) {
					if ((p->lockOrder > 0) && (p->exec == 0)) {
						break;
					}
					p = p->next;
				}

				if (p) {
					it = states.begin();
					ie = states.end();
					for (; it != ie; it++) {
						st = *it;
						if (st->pthreadId == p->threadId) {
							st->pc = st->prevPC;
							st->isWait = 0;
						}
					}
				} else {
					printf("程序死锁\n");
					checkRace();
					return;
				}

			}

		}
	}

	delete searcher;
	searcher = 0;

	dump: if (DumpStatesOnHalt && !states.empty()) {
		std::cerr << "KLEE: halting execution, dumping remaining states\n";
		for (std::set<ExecutionState*>::iterator it = states.begin(), ie =
				states.end(); it != ie; ++it) {
			ExecutionState &state = **it;
			stepInstruction(state); // keep stats rolling
			terminateStateEarly(state, "Execution halting.");
		}
		updateStates(0);
	}
}

std::string Executor::getAddressInfo(ExecutionState &state,
		ref<Expr> address) const {
	std::ostringstream info;
	info << "\taddress: " << address << "\n";
	uint64_t example;
	if (ConstantExpr * CE = dyn_cast<ConstantExpr>(address)) {
		example = CE->getZExtValue();
	} else {
		ref<ConstantExpr> value;
		bool success = solver->getValue(state, address, value);
		assert(success && "FIXME: Unhandled solver failure");
		(void) success;
		example = value->getZExtValue();
		info << "\texample: " << example << "\n";
		std::pair<ref<Expr>, ref<Expr> > res = solver->getRange(state,
				address);
		info << "\trange: [" << res.first << ", " << res.second << "]\n";
	}

	MemoryObject hack((unsigned) example);
	MemoryMap::iterator lower = state.addressSpace.objects.upper_bound(&hack);
	info << "\tnext: ";
	if (lower == state.addressSpace.objects.end()) {
		info << "none\n";
	} else {
		const MemoryObject *mo = lower->first;
		std::string alloc_info;
		mo->getAllocInfo(alloc_info);
		info << "object at " << mo->address << " of size " << mo->size
				<< "\n" << "\t\t" << alloc_info << "\n";
	}
	if (lower != state.addressSpace.objects.begin()) {
		--lower;
		info << "\tprev: ";
		if (lower == state.addressSpace.objects.end()) {
			info << "none\n";
		} else {
			const MemoryObject *mo = lower->first;
			std::string alloc_info;
			mo->getAllocInfo(alloc_info);
			info << "object at " << mo->address << " of size " << mo->size
					<< "\n" << "\t\t" << alloc_info << "\n";
		}
	}

	return info.str();
}

void Executor::terminateState(ExecutionState &state) {
	if (replayOut && replayPosition != replayOut->numObjects) {
		klee_warning_once(replayOut,
				"replay did not consume all objects in test input.");
	}

///cc,add for state exit check
//if thread exit when still hold locks, show a warning
	if (!state.threadLocks.empty()) {
		//std::cout << "warning: thread " << state.pthreadId
		//	<< " exit with locks hold" << std::endl;
	}
//remove thread from process
	//std::cout << "*********** thread " << state.pthreadId << " terminate."
	//	<< std::endl;
	if (state.processInfo != NULL) {
		if (state.processInfo->pthreads.find(&state)
				== state.processInfo->pthreads.end()) {
			//	std::cout << "warning: unknow thread exit." << std::endl;
		}
		state.processInfo->pthreads.erase(&state);
	}
///cc,end

	interpreterHandler->incPathsExplored();

	std::set<ExecutionState*>::iterator it = addedStates.find(&state);
	if (it == addedStates.end()) {
		state.pc = state.prevPC;

		removedStates.insert(&state);
	} else {
		// never reached searcher, just delete immediately
		std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it3 =
				seedMap.find(&state);
		if (it3 != seedMap.end())
			seedMap.erase(it3);
		addedStates.erase(it);
		processTree->remove(state.ptreeNode);
		delete &state;
	}
}

void Executor::terminateStateEarly(ExecutionState &state,
		const Twine &message) {
	if (!OnlyOutputStatesCoveringNew || state.coveredNew
			|| (AlwaysOutputSeeds && seedMap.count(&state)))
		interpreterHandler->processTestCase(state,
				(message + "\n").str().c_str(), "early");
	terminateState(state);
}

void Executor::terminateStateOnExit(ExecutionState &state) {
	if (!OnlyOutputStatesCoveringNew || state.coveredNew
			|| (AlwaysOutputSeeds && seedMap.count(&state)))
		interpreterHandler->processTestCase(state, 0, 0);
	terminateState(state);
}

void Executor::terminateStateOnError(ExecutionState &state,
		const llvm::Twine &messaget, const char *suffix,
		const llvm::Twine &info) {
	std::string message = messaget.str();
	static std::set<std::pair<Instruction*, std::string> > emittedErrors;
	const InstructionInfo &ii = *state.prevPC->info;

	if (EmitAllErrors
			|| emittedErrors.insert(
					std::make_pair(state.prevPC->inst, message)).second) {
		if (ii.file != "") {
			klee_message("ERROR: %s:%d: %s", ii.file.c_str(), ii.line,
					message.c_str());
		} else {
			klee_message("ERROR: %s", message.c_str());
		}
		if (!EmitAllErrors)
			klee_message(
					"NOTE: now ignoring this error at this location");

		std::ostringstream msg;
		msg << "Error: " << message << "\n";
		if (ii.file != "") {
			msg << "File: " << ii.file << "\n";
			msg << "Line: " << ii.line << "\n";
		}
		msg << "Stack: \n";
		state.dumpStack(msg);

		std::string info_str = info.str();
		if (info_str != "")
			msg << "Info: \n" << info_str;
		interpreterHandler->processTestCase(state, msg.str().c_str(),
				suffix);
	}

	terminateState(state);
}

// XXX shoot me
static const char *okExternalsList[] = { "printf", "fprintf", "puts", "getpid" };
static std::set<std::string> okExternals(okExternalsList,
		okExternalsList
				+ (sizeof(okExternalsList) / sizeof(okExternalsList[0])));

void Executor::callExternalFunction(ExecutionState &state, KInstruction *target,
		Function *function, std::vector<ref<Expr> > &arguments) {
// check if specialFunctionHandler wants it
	if (specialFunctionHandler->handle(state, function, target, arguments))
		return;

	if (NoExternals && !okExternals.count(function->getName())) {
		std::cerr << "KLEE:ERROR: Calling not-OK external function : "
				<< function->getName().str() << "\n";
		terminateStateOnError(state, "externals disallowed", "user.err");
		return;
	}

// normal external function handling path
// allocate 128 bits for each argument (+return value) to support fp80's;
// we could iterate through all the arguments first and determine the exact
// size we need, but this is faster, and the memory usage isn't significant.
	uint64_t *args = (uint64_t*) alloca(
			2 * sizeof(*args) * (arguments.size() + 1));
	memset(args, 0, 2 * sizeof(*args) * (arguments.size() + 1));
	unsigned wordIndex = 2;
	for (std::vector<ref<Expr> >::iterator ai = arguments.begin(), ae =
			arguments.end(); ai != ae; ++ai) {
		if (AllowExternalSymCalls) { // don't bother checking uniqueness
			ref<ConstantExpr> ce;
			bool success = solver->getValue(state, *ai, ce);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			ce->toMemory(&args[wordIndex]);
			wordIndex += (ce->getWidth() + 63) / 64;
		} else {
			ref<Expr> arg = toUnique(state, *ai);
			if (ConstantExpr * ce = dyn_cast<ConstantExpr>(arg)) {
				// XXX kick toMemory functions from here
				ce->toMemory(&args[wordIndex]);
				wordIndex += (ce->getWidth() + 63) / 64;
			} else {
				terminateStateOnExecError(state,
						"external call with symbolic argument: "
								+ function->getName());
				return;
			}
		}
	}

	state.addressSpace.copyOutConcretes();

	if (!SuppressExternalWarnings) {
		std::ostringstream os;
		os << "calling external: " << function->getName().str() << "(";
		for (unsigned i = 0; i < arguments.size(); i++) {
			os << arguments[i];
			if (i != arguments.size() - 1)
				os << ", ";
		}
		os << ")";

		if (AllExternalWarnings)
			klee_warning("%s", os.str().c_str());
		else
			klee_warning_once(function, "%s", os.str().c_str());
	}

	bool success = externalDispatcher->executeCall(function, target->inst,
			args);
	if (!success) {
		terminateStateOnError(state,
				"failed external call: " + function->getName(),
				"external.err");
		return;
	}

	if (!state.addressSpace.copyInConcretes()) {
		terminateStateOnError(state, "external modified read-only object",
				"external.err");
		return;
	}

	LLVM_TYPE_Q
	Type *resultType = target->inst->getType();
	if (resultType != Type::getVoidTy(getGlobalContext())) {
		ref<Expr> e = ConstantExpr::fromMemory((void*) args,
				getWidthForLLVMType(resultType));
		bindLocal(target, state, e);
	}
}

/***/

ref<Expr> Executor::replaceReadWithSymbolic(ExecutionState &state,
		ref<Expr> e) {
	unsigned n = interpreterOpts.MakeConcreteSymbolic;
	if (!n || replayOut || replayPath)
		return e;

// right now, we don't replace symbolics (is there any reason too?)
	if (!isa<ConstantExpr>(e))
		return e;

	if (n != 1 && random() % n)
		return e;

// create a new fresh location, assert it is equal to concrete value in e
// and return it.

	static unsigned id;
	const Array *array = new Array("rrws_arr" + llvm::utostr(++id),
			Expr::getMinBytesForWidth(e->getWidth()));
	ref<Expr> res = Expr::createTempRead(array, e->getWidth());
	ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(e, res));
	std::cerr << "Making symbolic: " << eq << "\n";
	state.addConstraint(eq);
	return res;
}

ObjectState *Executor::bindObjectInState(ExecutionState &state,
		const MemoryObject *mo, bool isLocal, const Array *array) {
	ObjectState *os =
			array ? new ObjectState(mo, array) : new ObjectState(mo);
	state.addressSpace.bindObject(mo, os);

// Its possible that multiple bindings of the same mo in the state
// will put multiple copies on this list, but it doesn't really
// matter because all we use this list for is to unbind the object
// on function return.
	if (isLocal)
		state.stack.back().allocas.push_back(mo);

	return os;
}

void Executor::executeAlloc(ExecutionState &state, ref<Expr> size, bool isLocal,
		KInstruction *target, bool zeroMemory,
		const ObjectState *reallocFrom) {
	size = toUnique(state, size);
	if (ConstantExpr * CE = dyn_cast<ConstantExpr>(size)) {
		MemoryObject *mo = memory->allocate(CE->getZExtValue(), isLocal,
				false, state.prevPC->inst);
		if (!mo) {
			bindLocal(target, state,
					ConstantExpr::alloc(0,
							Context::get().getPointerWidth()));
		} else {
			///cc,add malloc info to state
			if (isLocal == false) {
				///cc,print malloc object info
// 				std::cout << std::string(state.prevPC->inst->getOpcodeName()) << std::endl;
// 				std::cout << state.prevPC->inst->getParent()->getNameStr() << std::endl;
// 				std::cout << state.prevPC->inst->getParent()->getParent()->getNameStr() << std::endl;
// 				std::cout << state.prevPC->inst->getParent()->getParent()->getParent()->getModuleIdentifier() << std::endl;
				state.processInfo->insertMalloc(mo->address, mo);
			}
			ObjectState *os = bindObjectInState(state, mo, isLocal);
			if (zeroMemory) {
				os->initializeToZero();
			} else {
				os->initializeToRandom();
			}
			bindLocal(target, state, mo->getBaseExpr());

			if (reallocFrom) {
				unsigned count = std::min(reallocFrom->size, os->size);
				for (unsigned i = 0; i < count; i++)
					os->write(i, reallocFrom->read8(i));
				state.addressSpace.unbindObject(
						reallocFrom->getObject());
			}
		}
	} else {
		// XXX For now we just pick a size. Ideally we would support
		// symbolic sizes fully but even if we don't it would be better to
		// "smartly" pick a value, for example we could fork and pick the
		// min and max values and perhaps some intermediate (reasonable
		// value).
		//
		// It would also be nice to recognize the case when size has
		// exactly two values and just fork (but we need to get rid of
		// return argument first). This shows up in pcre when llvm
		// collapses the size expression with a select.

		ref<ConstantExpr> example;
		bool success = solver->getValue(state, size, example);
		assert(success && "FIXME: Unhandled solver failure");
		(void) success;

		// Try and start with a small example.
		Expr::Width W = example->getWidth();
		while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
			ref<ConstantExpr> tmp = example->LShr(
					ConstantExpr::alloc(1, W));
			bool res;
			bool success = solver->mayBeTrue(state,
					EqExpr::create(tmp, size), res);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			if (!res)
				break;
			example = tmp;
		}

		StatePair fixedSize = fork(state, EqExpr::create(example, size),
				true);

		if (fixedSize.second) {
			// Check for exactly two values
			ref<ConstantExpr> tmp;
			bool success = solver->getValue(*fixedSize.second, size, tmp);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			bool res;
			success = solver->mustBeTrue(*fixedSize.second,
					EqExpr::create(tmp, size), res);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			if (res) {
				executeAlloc(*fixedSize.second, tmp, isLocal, target,
						zeroMemory, reallocFrom);
			} else {
				// See if a *really* big value is possible. If so assume
				// malloc will fail for it, so lets fork and return 0.
				StatePair hugeSize = fork(*fixedSize.second,
						UltExpr::create(
								ConstantExpr::alloc(1 << 31, W),
								size), true);
				if (hugeSize.first) {
					klee_message(
							"NOTE: found huge malloc, returning 0");
					bindLocal(target, *hugeSize.first,
							ConstantExpr::alloc(0,
									Context::get().getPointerWidth()));
				}

				if (hugeSize.second) {
					std::ostringstream info;
					ExprPPrinter::printOne(info, "  size expr", size);
					info << "  concretization : " << example << "\n";
					info << "  unbound example: " << tmp << "\n";
					terminateStateOnError(*hugeSize.second,
							"concretized symbolic size",
							"model.err", info.str());
				}
			}
		}

		if (fixedSize.first) // can be zero when fork fails
			executeAlloc(*fixedSize.first, example, isLocal, target,
					zeroMemory, reallocFrom);
	}
}

void Executor::executeFree(ExecutionState &state, ref<Expr> address,
		KInstruction *target) {
	StatePair zeroPointer = fork(state, Expr::createIsZero(address), true);
	if (zeroPointer.first) {
		if (target)
			bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
	}
	if (zeroPointer.second) { // address != 0
		ExactResolutionList rl;
		resolveExact(*zeroPointer.second, address, rl, "free");

		for (Executor::ExactResolutionList::iterator it = rl.begin(), ie =
				rl.end(); it != ie; ++it) {
			const MemoryObject *mo = it->first.first;
			if (mo->isLocal) {
				terminateStateOnError(*it->second, "free of alloca",
						"free.err",
						getAddressInfo(*it->second, address));
			} else if (mo->isGlobal) {
				terminateStateOnError(*it->second, "free of global",
						"free.err",
						getAddressInfo(*it->second, address));
			} else {
				it->second->addressSpace.unbindObject(mo);
				if (target)
					bindLocal(target, *it->second,
							Expr::createPointer(0));
			}
		}
	}
}

void Executor::resolveExact(ExecutionState &state, ref<Expr> p,
		ExactResolutionList &results, const std::string &name) {
// XXX we may want to be capping this?
	ResolutionList rl;
	state.addressSpace.resolve(state, solver, p, rl);

	ExecutionState *unbound = &state;
	for (ResolutionList::iterator it = rl.begin(), ie = rl.end(); it != ie;
			++it) {
		ref<Expr> inBounds = EqExpr::create(p, it->first->getBaseExpr());

		StatePair branches = fork(*unbound, inBounds, true);

		if (branches.first)
			results.push_back(std::make_pair(*it, branches.first));

		unbound = branches.second;
		if (!unbound) // Fork failure
			break;
	}

	if (unbound) {
		terminateStateOnError(*unbound,
				"memory error: invalid pointer: " + name, "ptr.err",
				getAddressInfo(*unbound, p));
	}
}

void Executor::executeMemoryOperation(ExecutionState &state, bool isWrite,
		ref<Expr> address, ref<Expr> value /* undef if read */,
		KInstruction *target /* undef if write */) {
	Expr::Width type = (
			isWrite ? value->getWidth() : getWidthForLLVMType(
							target->inst->getType()));
	unsigned bytes = Expr::getMinBytesForWidth(type);

	if (SimplifySymIndices) {
		if (!isa<ConstantExpr>(address))
			address = state.constraints.simplifyExpr(address);
		if (isWrite && !isa<ConstantExpr>(value))
			value = state.constraints.simplifyExpr(value);
	}

// fast path: single in-bounds resolution
	ObjectPair op;
	bool success;
	solver->setTimeout(stpTimeout);
	if (!state.addressSpace.resolveOne(state, solver, address, op, success)) {
		address = toConstant(state, address, "resolveOne failure");
		success = state.addressSpace.resolveOne(cast<ConstantExpr>(address),
				op);
	}
	solver->setTimeout(0);

	if (success) {
		const MemoryObject *mo = op.first;

		if (MaxSymArraySize && mo->size >= MaxSymArraySize) {
			address = toConstant(state, address, "max-sym-array-size");
		}

		ref<Expr> offset = mo->getOffsetExpr(address);

		bool inBounds;
		solver->setTimeout(stpTimeout);
		bool success = solver->mustBeTrue(state,
				mo->getBoundsCheckOffset(offset, bytes), inBounds);
		solver->setTimeout(0);
		if (!success) {
			state.pc = state.prevPC;
			terminateStateEarly(state, "Query timed out (bounds check).");
			return;
		}

		if (inBounds) {
			const ObjectState *os = op.second;
			if (isWrite) {
				if (os->readOnly) {
					terminateStateOnError(state,
							"memory error: object read only",
							"readonly.err");
				} else {
					ObjectState *wos =
							state.addressSpace.getWriteable(mo,
									os);
					wos->write(offset, value);
				}
			} else {
				ref<Expr> result = os->read(offset, type);

				if (interpreterOpts.MakeConcreteSymbolic)
					result = replaceReadWithSymbolic(state, result);

				bindLocal(target, state, result);
			}

			return;
		}
	}

// we are on an error path (no resolution, multiple resolution, one
// resolution with out of bounds)

	ResolutionList rl;
	solver->setTimeout(stpTimeout);
	bool incomplete = state.addressSpace.resolve(state, solver, address, rl,
			0, stpTimeout);
	solver->setTimeout(0);

// XXX there is some query wasteage here. who cares?
	ExecutionState *unbound = &state;

	for (ResolutionList::iterator i = rl.begin(), ie = rl.end(); i != ie;
			++i) {
		const MemoryObject *mo = i->first;
		const ObjectState *os = i->second;
		ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);

		StatePair branches = fork(*unbound, inBounds, true);
		ExecutionState *bound = branches.first;

		// bound can be 0 on failure or overlapped
		if (bound) {
			if (isWrite) {
				if (os->readOnly) {
					terminateStateOnError(*bound,
							"memory error: object read only",
							"readonly.err");
				} else {
					ObjectState *wos =
							bound->addressSpace.getWriteable(mo,
									os);
					wos->write(mo->getOffsetExpr(address), value);
				}
			} else {
				ref<Expr> result = os->read(mo->getOffsetExpr(address),
						type);
				bindLocal(target, *bound, result);
			}
		}

		unbound = branches.second;
		if (!unbound)
			break;
	}

// XXX should we distinguish out of bounds and overlapped cases?
	if (unbound) {
		if (incomplete) {
			terminateStateEarly(*unbound, "Query timed out (resolve).");
		} else {
			terminateStateOnError(*unbound,
					"memory error: out of bound pointer", "ptr.err",
					getAddressInfo(*unbound, address));
		}
	}
}

void Executor::executeMakeSymbolic(ExecutionState &state,
		const MemoryObject *mo, const std::string &name) {
// Create a new object state for the memory object (instead of a copy).
	if (!replayOut) {
		// Find a unique name for this array.  First try the original name,
		// or if that fails try adding a unique identifier.
		unsigned id = 0;
		std::string uniqueName = name;
		while (!state.arrayNames.insert(uniqueName).second) {
			uniqueName = name + "_" + llvm::utostr(++id);
		}
		const Array *array = new Array(uniqueName, mo->size);
		bindObjectInState(state, mo, false, array);
		state.addSymbolic(mo, array);

		std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it =
				seedMap.find(&state);
		if (it != seedMap.end()) { // In seed mode we need to add this as a
						   // binding.
			for (std::vector<SeedInfo>::iterator siit =
					it->second.begin(), siie = it->second.end();
					siit != siie; ++siit) {
				SeedInfo &si = *siit;
				KTestObject *obj = si.getNextInput(mo,
						NamedSeedMatching);

				if (!obj) {
					if (ZeroSeedExtension) {
						std::vector<unsigned char> &values =
								si.assignment.bindings[array];
						values = std::vector<unsigned char>(
								mo->size, '\0');
					} else if (!AllowSeedExtension) {
						terminateStateOnError(state,
								"ran out of inputs during seeding",
								"user.err");
						break;
					}
				} else {
					if (obj->numBytes != mo->size
							&& ((!(AllowSeedExtension
									|| ZeroSeedExtension)
									&& obj->numBytes
											< mo->size)
									|| (!AllowSeedTruncation
											&& obj->numBytes
													> mo->size))) {
						std::stringstream msg;
						msg << "replace size mismatch: " << mo->name
								<< "[" << mo->size << "]"
								<< " vs " << obj->name << "["
								<< obj->numBytes << "]"
								<< " in test\n";

						terminateStateOnError(state, msg.str(),
								"user.err");
						break;
					} else {
						std::vector<unsigned char> &values =
								si.assignment.bindings[array];
						values.insert(values.begin(), obj->bytes,
								obj->bytes
										+ std::min(
												obj->numBytes,
												mo->size));
						if (ZeroSeedExtension) {
							for (unsigned i = obj->numBytes;
									i < mo->size; ++i)
								values.push_back('\0');
						}
					}
				}
			}
		}
	} else {
		ObjectState *os = bindObjectInState(state, mo, false);
		if (replayPosition >= replayOut->numObjects) {
			terminateStateOnError(state, "replay count mismatch",
					"user.err");
		} else {
			KTestObject *obj = &replayOut->objects[replayPosition++];
			if (obj->numBytes != mo->size) {
				terminateStateOnError(state, "replay size mismatch",
						"user.err");
			} else {
				for (unsigned i = 0; i < mo->size; i++)
					os->write8(i, obj->bytes[i]);
			}
		}
	}
}

/***/

void Executor::runFunctionAsMain(Function *f, int argc, char **argv,
		char **envp) {

	/*------------------------------------------------------------*/
	/* add by wanqizhi*/
//静态分析部分，取出其目标块和中间块
//	char ch;
//	printf("Do you want InitObjectBlock:");
//	scanf("%c", &ch);
//
//	if (ch == 'y' || ch == 'Y') {
//		main1();
//	} else {
//		printf("you don't init the ObjcetBlock\n");
//	}
//	/*------------------------------------------------------------*/
//
//	for (int aa = 0; aa < GobjectBlock.size(); aa++) {
//		std::cout << GobjectBlock[aa].pFunName << ", "
//				<< GobjectBlock[aa].pLabelName << ", "
//				<< GobjectBlock[aa].pStartLineNo << ", "
//				<< GobjectBlock[aa].pEndLineNo << std::endl;
//
//		TargetObject tarobj;
//		tarobj.functionName = GobjectBlock[aa].pFunName;
//		tarobj.basicBlockName = GobjectBlock[aa].pLabelName;
//
//		CFunLineRange cflr = GetFunRangeObj(GobjectBlock[aa].pStartLineNo);
//
//		CLabelInformation cli = GetLabelObj(cflr.pFunNo,
//				GobjectBlock[aa].pStartLineNo);
//
//		std::cout << "函数名：" << cflr.pFunName << ",函数编号:" << cflr.pFunNo
//				<< ",函数起始号" << cflr.pStartLineNo << ",函数终止号" << cflr.pEndLineNo
//				<< std::endl;
//
//		std::cout << "基本块名：" << cli.pLabelValue << ",块起始编号:" << cli.pStartLineNo
//				<< ",块结束编号" << cli.pEndLineNo << std::endl;
//
//		if (GobjectBlock[aa].pStartLineNo == GobjectBlock[aa].pEndLineNo) {
//			tarobj.offset = GobjectBlock[aa].pEndLineNo - cli.pStartLineNo;
//		} else {
//			tarobj.offset = GobjectBlock[aa].pEndLineNo - cli.pStartLineNo - 1;
//		}
//
//		std::cout << "functionName=" << tarobj.functionName << std::endl;
//		std::cout << "basicBlockName=" << tarobj.basicBlockName << std::endl;
//		std::cout << "offset=" << tarobj.offset << std::endl;
//
//		targetobjects.push_back(tarobj);
//	}
//
//	getchar();
//hml上面为解析目标块的功能
	/* 加入程序监控功能*/
	/*------------------------------------------------------------*/
//监控信息部分
	/*
	 char ch;
	 printf("Do you want get monitor message?:");
	 scanf("%c", &ch);

	 if (ch == 'y' || ch == 'Y')
	 {
	 isMonitor = 1;
	 char programName[100];
	 memset(programName, 0, 100);
	 strcpy(programName, "/home/administrator/sourceFile/");
	 getProgramName(argv[0], strlen(argv[0]), programName,
	 strlen(programName));

	 if (head != NULL)
	 {
	 std::cout << "原先head值没有清理\n";
	 delExecutionInfo();
	 }

	 getExecutionInfo();
	 //		checkExecutionInfo();
	 current = head;
	 exePthreadInfo *p = head;
	 while (p != NULL)
	 {
	 printf("线程:%d,类型:%d,互斥量:%d,顺序%d，标记:%d\n", p->threadId, p->type,
	 p->mutexAddr, p->lockOrder, p->disableFlag);
	 p = p->next;
	 }
	 getchar();
	 //		InitDataStruct(programName);
	 //		getLLNum(programName);

	 }
	 else
	 {
	 isMonitor = 0;
	 printf("-------you do not get the monotor message------\n");
	 }
	 */
	/*------------------------------------------------------------*/


	//初始化monitor监视器
	monitor_init();

	isMonitor = 0;
	std::vector<ref<Expr> > arguments;

// force deterministic initialization of memory objects
	srand(1);
	srandom(1);

	MemoryObject *argvMO = 0;

// In order to make uclibc happy and be closer to what the system is
// doing we lay out the environments at the end of the argv array
// (both are terminated by a null). There is also a final terminating
// null that uclibc seems to expect, possibly the ELF header?

	int envc;
	for (envc = 0; envp[envc]; ++envc)
		;

	unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
	KFunction *kf = kmodule->functionMap[f];
	assert(kf);
	Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
	if (ai != ae) {
		arguments.push_back(ConstantExpr::alloc(argc, Expr::Int32));

		if (++ai != ae) {
			///cc，为函数参数分配空间（分配时属性为全局，实际可以为局部）
			//      argvMO = memory->allocate((argc+1+envc+1+1) * NumPtrBytes, false, true,
			// 		 f->begin()->begin());
			argvMO = memory->allocate(
					(argc + 1 + envc + 1 + 1) * NumPtrBytes, true,
					false, f->begin()->begin());

			arguments.push_back(argvMO->getBaseExpr());

			if (++ai != ae) {
				uint64_t envp_start = argvMO->address
						+ (argc + 1) * NumPtrBytes;
				arguments.push_back(Expr::createPointer(envp_start));

				if (++ai != ae)
					klee_error(
							"invalid main function (expect 0-3 arguments)");
			}
		}
	}

	//--------此段代码用于检测可能数据竞争的位置----------
//	char c;
//	 printf("Do you want to check all the places which may produce data race?:");
//	scanf("%c", &c);
//
//	if (c == 'y' || c == 'Y')
//	{
//		checkDR = true;
//		drc = new DataRaceChecking();
//	}
//	else
//		checkDR = false;
	checkDR = false;
	//-------------------------------------------------------------------

	//--------此段代码用于重放的初始化-------------------------------

	replayOrNot = false;
	if(replayOrNot)
	{
		printf("It is a Replay!\n");
		replay = new Replay();
		replay->ReadFile();
		replay->initPthreadEvent();
	}
	//---------------------------------------------------------------------

	ExecutionState *state = new ExecutionState(kmodule->functionMap[f]);

///cc,add for build processInfo
	state->setPathId(0);

	if (pathWriter)
		state->pathOS = pathWriter->open();
	if (symPathWriter)
		state->symPathOS = symPathWriter->open();

	if (statsTracker)
		statsTracker->framePushed(*state, 0);

	assert( arguments.size() == f->arg_size() && "wrong number of arguments");
	for (unsigned i = 0, e = f->arg_size(); i != e; ++i)
		bindArgument(kf, i, *state, arguments[i]);

	if (argvMO) {
		ObjectState *argvOS = bindObjectInState(*state, argvMO, false);

		for (int i = 0; i < argc + 1 + envc + 1 + 1; i++) {
			MemoryObject *arg;

			if (i == argc || i >= argc + 1 + envc) {
				arg = 0;
			} else {
				char *s = i < argc ? argv[i] : envp[i - (argc + 1)];
				int j, len = strlen(s);
				///cc,使参数为局部变量
				//        arg = memory->allocate(len+1, false, true, state->pc->inst);
				arg = memory->allocate(len + 1, true, false,
						state->pc->inst);
				ObjectState *os = bindObjectInState(*state, arg, false);
				for (j = 0; j < len + 1; j++)
					os->write8(j, s[j]);
			}

			if (arg) {
				argvOS->write(i * NumPtrBytes, arg->getBaseExpr());
			} else {
				argvOS->write(i * NumPtrBytes, Expr::createPointer(0));
			}
		}
	}

	initializeGlobals(*state);

	processTree = new PTree(state);
	processTree->root->nodeId = Executor::createnodeId++;
	state->ptreeNode = processTree->root;
	run(*state);
	delete processTree;

	delete head;
//	delExecutionInfo();
	processTree = 0;
//	delete head;
	head = 0;
	current = 0;
	pre = 0;

	for (std::set<ExecutionImage*>::iterator it = executionImageList.begin(),
			ie = executionImageList.end(); it != ie; it++) {
		ExecutionImage *ei = *it;
		delete ei->head;
		ei->current = 0;
		ei->pre = 0;
		ei->head = 0;
	}

	executionImageList.clear();

	//wxf
//	for (vector<siamese_tag>::size_type i = 0; i != siamese_inst_index.size();
//			++i) {
//		std::cout << siamese_inst_index[i].line << " "
//				<< siamese_inst_index[i].siamese_flag << " "
//				<< siamese_inst_index[i].siamese_start_flag
//				<< std::endl;
//	}
	std::cout <<"全局变量总数以及各变量名和地址"<<std::endl;
	std::cout <<G_global_num<<std::endl;
	for (int i = 0; i != G_global_num;++i)
	{
		printf("%s,%u\n", GSA_global_var[i].Sp_name, GSA_global_var[i].address);
	}
	//打印保存监控信息
	if(!replayOrNot)
	{
		//store_record();
	}
	display_record_info();
	//--------此段代码用于检测可能数据竞争的位置----------
	if(checkDR)
	{
		drc->CheckRace();
		delete(drc);
	}
	//-------------------------------------------------------------------
	//wxf

//hlm to clear
	threadList.clear();
	deletedNodes.clear();
	targetobjects.clear();

// hack to clear memory objects
	delete memory;
	memory = new MemoryManager();

	globalObjects.clear();
	globalAddresses.clear();
	states.clear();
	addedStates.clear();
	removedStates.clear();

	if (statsTracker)
		statsTracker->done();
}

unsigned Executor::getPathStreamID(const ExecutionState &state) {
	assert(pathWriter);
	return state.pathOS.getID();
}

unsigned Executor::getSymbolicPathStreamID(const ExecutionState &state) {
	assert(symPathWriter);
	return state.symPathOS.getID();
}

void Executor::getConstraintLog(const ExecutionState &state, std::string &res,
		Interpreter::LogType logFormat) {

	std::ostringstream info;

	switch (logFormat) {
	case STP: {
		Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
		char *log = solver->stpSolver->getConstraintLog(query);
		res = std::string(log);
		free(log);
	}
		break;

	case KQUERY: {
		std::ostringstream info;
		ExprPPrinter::printConstraints(info, state.constraints);
		res = info.str();
	}
		break;

	case SMTLIB2: {
		std::ostringstream info;
		ExprSMTLIBPrinter* printer = createSMTLIBPrinter();
		printer->setOutput(info);
		Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
		printer->setQuery(query);
		printer->generateOutput();
		res = info.str();
		delete printer;
	}
		break;

	default:
		klee_warning(
				"Executor::getConstraintLog() : Log format not supported!");
	}

}

bool Executor::getSymbolicSolution(const ExecutionState &state,
		std::vector<std::pair<std::string, std::vector<unsigned char> > > &res) {
	solver->setTimeout(stpTimeout);

	ExecutionState tmp(state);
	if (!NoPreferCex) {
		for (unsigned i = 0; i != state.symbolics.size(); ++i) {
			const MemoryObject *mo = state.symbolics[i].first;
			std::vector<ref<Expr> >::const_iterator pi =
					mo->cexPreferences.begin(), pie =
					mo->cexPreferences.end();
			for (; pi != pie; ++pi) {
				bool mustBeTrue;
				bool success = solver->mustBeTrue(tmp,
						Expr::createIsZero(*pi), mustBeTrue);
				if (!success)
					break;
				if (!mustBeTrue)
					tmp.addConstraint(*pi);
			}
			if (pi != pie)
				break;
		}
	}

	std::vector<std::vector<unsigned char> > values;
	std::vector<const Array*> objects;
	for (unsigned i = 0; i != state.symbolics.size(); ++i)
		objects.push_back(state.symbolics[i].second);
	bool success = solver->getInitialValues(tmp, objects, values);
	solver->setTimeout(0);
	if (!success) {
		klee_warning(
				"unable to compute initial values (invalid constraints?)!");
		ExprPPrinter::printQuery(std::cerr, state.constraints,
				ConstantExpr::alloc(0, Expr::Bool));
		return false;
	}

	for (unsigned i = 0; i != state.symbolics.size(); ++i)
		res.push_back(
				std::make_pair(state.symbolics[i].first->name,
						values[i]));
	return true;
}

void Executor::getCoveredLines(const ExecutionState &state,
		std::map<const std::string*, std::set<unsigned> > &res) {
	res = state.coveredLines;
}

void Executor::doImpliedValueConcretization(ExecutionState &state, ref<Expr> e,
		ref<ConstantExpr> value) {
	abort(); // FIXME: Broken until we sort out how to do the write back.

	if (DebugCheckForImpliedValues)
		ImpliedValue::checkForImpliedValues(solver->solver, e, value);

	ImpliedValueList results;
	ImpliedValue::getImpliedValues(e, value, results);
	for (ImpliedValueList::iterator it = results.begin(), ie = results.end();
			it != ie; ++it) {
		ReadExpr *re = it->first.get();

		if (ConstantExpr * CE = dyn_cast<ConstantExpr>(re->index)) {
			// FIXME: This is the sole remaining usage of the Array object
			// variable. Kill me.
			const MemoryObject *mo = 0; //re->updates.root->object;
			const ObjectState *os = state.addressSpace.findObject(mo);

			if (!os) {
				// object has been free'd, no need to concretize (although as
				// in other cases we would like to concretize the outstanding
				// reads, but we have no facility for that yet)
			} else {
				assert(
						!os->readOnly && "not possible? read only object with static read?");
				ObjectState *wos = state.addressSpace.getWriteable(mo,
						os);
				wos->write(CE, it->second);
			}
		}
	}
}

Expr::Width Executor::getWidthForLLVMType(LLVM_TYPE_Q llvm::Type *type) const {
	return kmodule->targetData->getTypeSizeInBits(type);
}

///

Interpreter *Interpreter::create(const InterpreterOptions &opts,
		InterpreterHandler *ih) {
	return new Executor(opts, ih);
}

//hlm
void Executor::rollBack(ExecutionState *state, ExecutionSnapShot &snapshot) {

	int rbNodeId = snapshot.nodeId;
	int currentNodeId = state->ptreeNode->nodeId;

	PTree::Node *n = state->ptreeNode;
	PTree::Node *s = NULL;

	while ((n->nodeId != rbNodeId) && (n->parent->nodeId != rbNodeId)) {
		PTree::Node *p = n->parent;
		if (p) {

			if (n->data == 0) {
				deletedNodes.insert(n);
			} else {
				removedStates.insert(n->data);
			}
			if (n == p->left) {
				if (p->right) {
					preOrder(p->right);
				}
			} else {
				assert(n == p->right);
				if (p->left) {
					preOrder(p->left);
				}
			}
		}
		n = p;
	}

	if (n->parent->nodeId == rbNodeId) {
		if (n->data == 0) {
			deletedNodes.insert(n);
		} else {
			removedStates.insert(n->data);
		}
		s = n;
		n = n->parent;
	}

	if (currentNodeId == rbNodeId) {
		state->copyExecutionState(*snapshot.state);
	}

	if (s != NULL) {
		if (s == n->left) {
			if (n->right) {
				preOrder(n->right);
			}
		} else {
			assert(s == n->right);
			if (n->left) {
				preOrder(n->left);
			}
		}
	}

//	for (std::set<ExecutionState*>::iterator it = deletedStates.begin(), ie =
//			deletedStates.end(); it != ie; ++it)
//	{
//		ExecutionState *es = *it;
//		std::set<ExecutionState*>::iterator it2 = states.find(es);
//		assert(it2!=states.end());
//		states.erase(it2);
//
//		processTree->delNode(es->ptreeNode);
//		delete es;
//	}

//	if (searcher)
//	{
//		//searcher->
//		addedStates.insert(snapshot.state);
//		deletedStates.erase(state);
//		searcher->update(state, addedStates, deletedStates);
//		addedStates.clear();
//	}

//	deletedStates.clear();

	if (currentNodeId != rbNodeId) {
		addedStates.insert(snapshot.state);
		n->data = snapshot.state;
		snapshot.state->ptreeNode = n;
	}

//	states.insert(snapshot.state);

}

void Executor::preOrder(PTree::Node *n) {
	if (n) {
		preOrder(n->left);
		preOrder(n->right);

		//	std::cout << "节点号为" << n->nodeId << std::endl;
		if (n->data == 0) {
			deletedNodes.insert(n);
		} else {
			removedStates.insert(n->data);
		}
	}
}

//hlm

//wxf
void Executor::checkSiamese(ExecutionState state, KInstruction *ki) {

	char F_event_type;
	int F_global_var_id;
	int F_siamese;
	int F_source_line;
	int F_siamese_start;
	int F_thread_id;

	Instruction *i = ki->inst;
	//设置连同标志
	setSiameseFlag(state, ki, F_source_line, F_siamese, F_siamese_start);

	//LOAD指令
	if (i->getOpcode() == Instruction::Load) {

		ref<Expr> base = eval(ki, 0, state).value;
		ObjectPair op;
		bool success;
		solver->setTimeout(stpTimeout);
		if (!state.addressSpace.resolveOne(state, solver, base, op,
				success)) {
			base = toConstant(state, base, "resolveOne failure");
			success = state.addressSpace.resolveOne(
					cast<ConstantExpr>(base), op);
		}
		solver->setTimeout(0);

		if (success) {
			const MemoryObject *mo = op.first;

			ConstantExpr *CE = dyn_cast<ConstantExpr>(base);
			//std::cout<<"load: "<<(uint64_t *)RCE->getZExtValue()<<std::endl;
			uint64_t baseAddress = CE->getZExtValue();

			if (isGlobal(mo,baseAddress,F_global_var_id)) {
			//	std::cout << "global variable" << std::endl;
				//检查全局变量是否存入容器中
				//checkGlobalVarIndex(mo->name.c_str(), mo->address, F_global_var_id);

				//现在考虑到指针类型的全局变量，指针本身是一个全局变量
				//指针所指的内容也是全局变量
				//如果为指针类型，在llvm编译后的文件中，类型后面至少带有两个＊
				//现在的操作是不仅仅把指针的地址放入全局变量数组里面
				//还要把指针所指向的那块内存地址也放入全局变量数组
				string type_descprtion =
						i->getOperand(0)->getType()->getDescription();
				if (strstr(type_descprtion.c_str(), "**") != NULL) {
					std::cout << "pointer to pointer" << std::endl;

					Expr::Width type = getWidthForLLVMType(
							ki->inst->getType());
					unsigned bytes = Expr::getMinBytesForWidth(type);

					if (MaxSymArraySize
							&& mo->size >= MaxSymArraySize) {
						base = toConstant(state, base,
								"max-sym-array-size");
					}

					ref<Expr> offset = mo->getOffsetExpr(base);

					bool inBounds;
					solver->setTimeout(stpTimeout);
					bool success = solver->mustBeTrue(state,
							mo->getBoundsCheckOffset(offset,
									bytes), inBounds);
					solver->setTimeout(0);
					if (!success) {
						std::cout<< "Query timed out (bounds check)."<< std::endl;
						return;
					}

					if (inBounds) {
						const ObjectState *os = op.second;

						//读出该内存地址的内容，内容为指针所指向的内存的地址
						ref<Expr> result = os->read(offset, type);
						//非常重要，直接从ref<Expr>中获取地址！
						ConstantExpr *RCE = dyn_cast<ConstantExpr>(result);
						//std::cout<<"load: "<<(uint64_t *)RCE->getZExtValue()<<std::endl;
						uint64_t resultAddress = RCE->getZExtValue();
						int resMO_ID;
						string resMO_name = mo->name+"_ptr";
						checkGlobalVarIndex(resMO_name.c_str(), resultAddress, resMO_ID);
					}
				}//endif

				F_thread_id = state.pthreadId;
				F_event_type = 'r';

				MONITOR(F_thread_id,
						F_event_type, F_global_var_id, F_siamese,
						F_source_line, F_siamese_start);
			}

		}
	} else if (i->getOpcode() == Instruction::Store) {//STORE指令

//		llvm::outs()<<i->getOperand(0)->getType()->getDescription()<<",id:"<<i->getOperand(0)->getType()->getTypeID()<<"\n";
//		llvm::outs()<<i->getOperand(1)->getType()->getDescription()<<",id:"<<i->getOperand(1)->getType()->getTypeID()<<"\n";

		ref<Expr> base = eval(ki, 1, state).value;
		ref<Expr> value = eval(ki, 0, state).value;

		if (SimplifySymIndices) {
			if (!isa<ConstantExpr>(base))
				base = state.constraints.simplifyExpr(base);
		}

		ObjectPair op;
		bool success;
		solver->setTimeout(stpTimeout);
		if (!state.addressSpace.resolveOne(state, solver, base, op,
				success)) {
			base = toConstant(state, base, "resolveOne failure");
			success = state.addressSpace.resolveOne(
					cast<ConstantExpr>(base), op);
		}
		solver->setTimeout(0);

		if (success) {
			const MemoryObject *mo = op.first;

			ConstantExpr *CE = dyn_cast<ConstantExpr>(base);
			uint64_t baseAddress = CE->getZExtValue();


			if (isGlobal(mo, baseAddress, F_global_var_id)) {

				F_thread_id = state.pthreadId;

				//--------此段代码用于检测可能数据竞争的位置----------
				if(checkDR)
				{
					//printf("drc->AddNodeToRaceTree(%d,%d,%d,%d)\n",F_thread_id,F_global_var_id,F_source_line,F_siamese);
					drc->AddNodeToRaceTree(F_thread_id,F_global_var_id,F_source_line,F_siamese);
				}
				//-------------------------------------------------------------------

				F_event_type = 'w';
				MONITOR(F_thread_id,
						F_event_type, F_global_var_id, F_siamese,
						F_source_line, F_siamese_start);
			}
		}
	}
	else{
		//非读写操作，直接进行处理，类型为‘o’，操作的全局变量标号为-1
		MONITOR((unsigned long int) state.pthreadId,
								'o', -1, F_siamese,
								F_source_line, F_siamese_start);
	}
}

bool Executor::isGlobal(const MemoryObject *mo, uint64_t address, int &F_global_var_id)
{

	vector<unsigned>::size_type i;

	for ( i = 0; i < G_global_num; ++i) {
		if (GSA_global_var[i].address == address ) {
			F_global_var_id = i;
			return true;
		}
	}

	if(mo->isGlobal || mo->localToGlobal != 0)
	{
		//若地址与MO首地址有偏差，重新命名，命名方式为“原全局变量名称+偏差地址”
		if(mo->address != address )
		{
			char s[10];
			sprintf(s, "%d", address-mo->address);
			checkGlobalVarIndex((mo->name+s).c_str(), address, F_global_var_id);
			//std::cout<<"rename:"<<mo->name+s<<std::endl;
		}//endif
		else
			checkGlobalVarIndex(mo->name.c_str(), address, F_global_var_id);
		return true;
	}

	//endif

	return false;
}

//判断使用的全局变量是否已经保存在GSA_global_var数组中，没有就保存
void Executor::checkGlobalVarIndex(const char *name, uint64_t address, int &F_global_var_id) {

	char copyName[50];
	strcpy(copyName, name);
	vector<unsigned>::size_type i;
	for (i = 0; i < G_global_num; ++i) {
		if (GSA_global_var[i].address == address) {
			F_global_var_id = i;
			break;
		}
	}
	//查找不成功，新建全局变量结构体并初始化，加入数组中
	if (i >= G_global_num) {
		GS_global_var gbv;
		strcpy(gbv.Sp_name, copyName);
		gbv.address = address;
		GSA_global_var[G_global_num] = gbv;
		GSA_global_var[G_global_num].Sp_readset_head = NULL;
		GSA_global_var[G_global_num].Sp_writeset_head = NULL;
		GSA_global_var[G_global_num].G_siamese_start = 0;

		GSA_global_var[G_global_num].Sp_writets.Sp_timestamp_vector
			= (int*)malloc(sizeof(int)*pre_pthread_num);
		memset(GSA_global_var[G_global_num].Sp_writets.Sp_timestamp_vector,
				0,sizeof(int)*pre_pthread_num);

		GSA_global_var[G_global_num].Sp_readts.Sp_timestamp_vector
			= (int*)malloc(sizeof(int)*pre_pthread_num);
		memset(GSA_global_var[G_global_num].Sp_readts.Sp_timestamp_vector,
				0,sizeof(int)*pre_pthread_num);


		F_global_var_id = G_global_num;
		G_global_num++;
	}


	if (G_global_num >= GLOBAL_NUM) {
		GLOBAL_NUM += 20;
		//printf("AFTER ADD GLOBAL_NUM:%d\n",GLOBAL_NUM);
		GSA_global_var = (GS_global_var *) realloc(GSA_global_var,
				sizeof(GS_global_var)*GLOBAL_NUM );
		//--------此段代码用于检测可能数据竞争的位置----------
		if(checkDR)
			drc->AddGlobalVar();

		//---------------------------------------------------------------------

	}
}

void Executor::setSiameseFlag(ExecutionState state, KInstruction *ki,
		int &F_source_line, int &F_siamese, int &F_siamese_start) {

	Instruction *i = ki->inst;
	//获取当前指令的行号
	unsigned pcline = (*(ki->inst)).getDebugLoc().getLine();
	switch (i->getOpcode()) {
	case Instruction::Ret:
	case Instruction::Br:
	case Instruction::Call:
	case Instruction::Invoke: {
		F_source_line = pcline;
		if (Thread_info_index[state.pthreadId].siamese_start_flag == 1)
			F_siamese = 1;
		else
			F_siamese = 0;
		F_siamese_start = 0;
		Thread_info_index[state.pthreadId].siamese_start_flag = 0;
//		std::cout << "  line:" << pcline << "  s:" << F_siamese << " start:"
//				<< F_siamese_start << std::endl;
		return;
	}
	}
	//当前指令为ki，取前一条指令
	KInstruction *nextKi = state.pc;

	//获取下一条指令的行号
	unsigned nextpcline = (*(nextKi->inst)).getDebugLoc().getLine();
	//排除行号为0的指令
	if (pcline != 0) {
		if (pcline == nextpcline) {
			F_source_line = pcline;
			F_siamese = 1;
			F_siamese_start = 1;
			Thread_info_index[state.pthreadId].siamese_start_flag = 1;
		} else {
			F_source_line = pcline;
			if (Thread_info_index[state.pthreadId].siamese_start_flag == 1)
				F_siamese = 1;
			else
				F_siamese = 0;
			F_siamese_start = 0;
			Thread_info_index[state.pthreadId].siamese_start_flag = 0;
		}
	}

	//wxf
}
//wxf

bool Executor::checkInstructionForReplay(ExecutionState state, KInstruction *ki)
{

	int F_global_var_id;

	Instruction *i = ki->inst;

	//LOAD指令
	if (i->getOpcode() == Instruction::Load) {

		ref<Expr> base = eval(ki, 0, state).value;
		ObjectPair op;
		bool success;
		solver->setTimeout(stpTimeout);
		if (!state.addressSpace.resolveOne(state, solver, base, op,
				success)) {
			base = toConstant(state, base, "resolveOne failure");
			success = state.addressSpace.resolveOne(
					cast<ConstantExpr>(base), op);
		}
		solver->setTimeout(0);

		if (success) {
			const MemoryObject *mo = op.first;

			ConstantExpr *CE = dyn_cast<ConstantExpr>(base);
			//std::cout<<"load: "<<(uint64_t *)RCE->getZExtValue()<<std::endl;
			uint64_t baseAddress = CE->getZExtValue();

			if (isGlobal(mo,baseAddress,F_global_var_id)) {
			//	std::cout << "global variable" << std::endl;
				//检查全局变量是否存入容器中
				//checkGlobalVarIndex(mo->name.c_str(), mo->address, F_global_var_id);

				//现在考虑到指针类型的全局变量，指针本身是一个全局变量
				//指针所指的内容也是全局变量
				//如果为指针类型，在llvm编译后的文件中，类型后面至少带有两个＊
				//现在的操作是不仅仅把指针的地址放入全局变量数组里面
				//还要把指针所指向的那块内存地址也放入全局变量数组
				string type_descprtion =
						i->getOperand(0)->getType()->getDescription();
				if (strstr(type_descprtion.c_str(), "**") != NULL) {
					std::cout << "pointer to pointer" << std::endl;

					Expr::Width type = getWidthForLLVMType(
							ki->inst->getType());
					unsigned bytes = Expr::getMinBytesForWidth(type);

					if (MaxSymArraySize
							&& mo->size >= MaxSymArraySize) {
						base = toConstant(state, base,
								"max-sym-array-size");
					}

					ref<Expr> offset = mo->getOffsetExpr(base);

					bool inBounds;
					solver->setTimeout(stpTimeout);
					bool success = solver->mustBeTrue(state,
							mo->getBoundsCheckOffset(offset,
									bytes), inBounds);
					solver->setTimeout(0);
					if (!success) {
						std::cout<< "Query timed out (bounds check)."<< std::endl;
						return false;
					}

					if (inBounds) {
						const ObjectState *os = op.second;

						//读出该内存地址的内容，内容为指针所指向的内存的地址
						ref<Expr> result = os->read(offset, type);
						//非常重要，直接从ref<Expr>中获取地址！
						ConstantExpr *RCE = dyn_cast<ConstantExpr>(result);
						//std::cout<<"load: "<<(uint64_t *)RCE->getZExtValue()<<std::endl;
						uint64_t resultAddress = RCE->getZExtValue();
						int resMO_ID;
						string resMO_name = mo->name+"_ptr";
						checkGlobalVarIndex(resMO_name.c_str(), resultAddress, resMO_ID);
						return true;
					}
				}//endif
				return true;
			}
			else
				return false;
		}
	} else if (i->getOpcode() == Instruction::Store) {//STORE指令

//		llvm::outs()<<i->getOperand(0)->getType()->getDescription()<<",id:"<<i->getOperand(0)->getType()->getTypeID()<<"\n";
//		llvm::outs()<<i->getOperand(1)->getType()->getDescription()<<",id:"<<i->getOperand(1)->getType()->getTypeID()<<"\n";

		ref<Expr> base = eval(ki, 1, state).value;
		ref<Expr> value = eval(ki, 0, state).value;

		if (SimplifySymIndices) {
			if (!isa<ConstantExpr>(base))
				base = state.constraints.simplifyExpr(base);
		}

		ObjectPair op;
		bool success;
		solver->setTimeout(stpTimeout);
		if (!state.addressSpace.resolveOne(state, solver, base, op,
				success)) {
			base = toConstant(state, base, "resolveOne failure");
			success = state.addressSpace.resolveOne(
					cast<ConstantExpr>(base), op);
		}
		solver->setTimeout(0);

		if (success) {
			const MemoryObject *mo = op.first;

			ConstantExpr *CE = dyn_cast<ConstantExpr>(base);
			uint64_t baseAddress = CE->getZExtValue();

			if (isGlobal(mo, baseAddress, F_global_var_id)) {
				return true;
			}
			else
				return false;
		}
	}
	else
		return false;
}


bool Executor::updateSleepState()
{
	//wake up the sleep state
	long now;
	for(map<ExecutionState*,long>::iterator esit = sleepStates.begin();
			esit != sleepStates.end();
			esit++)
	{
		now = clock();
		if(esit->second <= now )
		{
			esit->first->canBeChose = true;
			sleepStates.erase(esit);
		}
	}

	for(set<ExecutionState*>::iterator it = states.begin(); it != states.end() ; it++)
	{
		if((*it)->canBeChose)
			return true;
	}
	return false;
}

void Executor::call_sleep(ExecutionState *state,unsigned int seconds)
{
	long startTime = clock();
	//在linux系统下，CLOCKS_PER_SEC的值可能有所不同，目前使用的linux打印出来的值是1000000
	long endTime = startTime + seconds*1000000;
	state->canBeChose = false;
	sleepStates.insert(map<ExecutionState*,long>::value_type(state,endTime));
}
