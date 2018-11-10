// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CROWN, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.
 
#include <assert.h>
#include <fstream>
#include <malloc.h>
#include <string>
#include <vector>
#include <map>
#include <iostream>
#include <sstream>
#include <stdarg.h>
#include <cstring>

#include "libcrown/symbolic_interpreter.h"
#include "base/basic_types.h"
#include "base/basic_functions.h"
#include "libcrown/crown.h"

using std::vector;
using std::map;
using namespace crown;
using namespace types;

// The symbolic interpreter.
static SymbolicInterpreter* SI = NULL;

static map<void *, void *> AddrMap;

// Have we read an input yet?  Until we have, generate only the
// minimal instrumentation necessary to track which branches were
// reached by the execution path.
static int pre_symbolic;

// Tables for converting from operators defined in libcrown/crown.h to
// those defined in base/basic_types.h.
static const int kOpTable[] = {
	// binary arithmetic
	ops::ADD, ops::SUBTRACT, ops::MULTIPLY,
	ops::DIV, ops::S_DIV, ops::MOD, ops::S_MOD,
	// binary bitwise operators
	ops::SHIFT_L, ops::SHIFT_R, ops::S_SHIFT_R,
	ops::BITWISE_AND, ops::BITWISE_OR, ops::BITWISE_XOR,
	// binary comparison
	ops::EQ, ops::NEQ,
	ops::GT, ops::S_GT, ops::LE, ops::S_LE,
	ops::LT, ops::S_LT, ops::GE, ops::S_GE,
	// unhandled binary operators (note: there aren't any)
	ops::CONCRETE,
	// unary operators
	ops::NEGATE, ops::BITWISE_NOT, ops::LOGICAL_NOT,
	ops::UNSIGNED_CAST, ops::SIGNED_CAST,
	// pointer operators
	ops::ADD_PI, ops::S_ADD_PI,
	ops::SUBTRACT_PI, ops::S_SUBTRACT_PI,
	ops::SUBTRACT_PP,
};

static char caller[256], callee[256];
static int enable_symbolic = 1;

static void __CrownAtExit();

#ifdef MALLOC_HOOK_ENABLED
// CROWN hooks for malloc functions.
static void crown_init_hook(void);
static void* crown_malloc_hook(size_t, const void*);
static void* crown_realloc_hook(void*, size_t, const void*);
static void crown_free_hook(void*, const void*);
static void* crown_memalign_hook(size_t, size_t, const void*);

// Original malloc hooks.
static void* (*orig_malloc_hook)(size_t, const void*);
static void* (*orig_realloc_hook)(void*, size_t, const void*);
static void (*orig_free_hook)(void*, const void*);
static void* (*orig_memalign_hook)(size_t, size_t, const void*);

// Make sure CROWN hooks are installed right after malloc is initialzed.
void (*__MALLOC_HOOK_VOLATILE __malloc_initialize_hook) (void) = crown_init_hook;

// Save original malloc hooks.
static inline void save_original_hooks(void) {
	orig_malloc_hook = __malloc_hook;
	orig_realloc_hook = __realloc_hook;
	orig_free_hook = __free_hook;
	orig_memalign_hook = __memalign_hook;
}

// Install CROWN hooks for malloc functions.
static inline void install_crown_hooks(void) {
	__malloc_hook = crown_malloc_hook;
	__realloc_hook = crown_realloc_hook;
	__free_hook = crown_free_hook;
	__memalign_hook = crown_memalign_hook;
}

// Restore original hooks for malloc functions.
static inline void restore_original_hooks(void) {
	__malloc_hook = orig_malloc_hook;
	__realloc_hook = orig_realloc_hook;
	__free_hook = orig_free_hook;
	__memalign_hook = orig_memalign_hook;
}

// After malloc initialization, save original hooks and install CROWN hooks.
static void crown_init_hook(void) {
	save_original_hooks();
	install_crown_hooks();
}

static void* crown_malloc_hook (size_t size, const void* caller) {
	restore_original_hooks();
	void* result = malloc (size);
	if (SI && result) {
		SI->Alloc(-1, (__CROWN_ADDR)result, size);
	}
	save_original_hooks();
	install_crown_hooks();
	return result;
}

static void* crown_realloc_hook(void* p, size_t size, const void* caller) {
	restore_original_hooks();
	void* result = realloc(p, size);
	if (SI) {
		//SI->Realloc( , , );
		SI->Free(-1, (__CROWN_ADDR)p);
		if (result) {
			SI->Alloc(-1, (__CROWN_ADDR)result, size);
		}
	}
	save_original_hooks();
	install_crown_hooks();
	return result;
}

static void crown_free_hook (void* p, const void* caller) {
	restore_original_hooks();
	// Record free.
	if (SI) {
		SI->Free(-1, (__CROWN_ADDR)p);
	}
	free(p);
	save_original_hooks();
	install_crown_hooks();
}

static void* crown_memalign_hook(size_t align, size_t size, const void* caller) {
	restore_original_hooks();
	void* result = memalign(align, size);
	// Record allocation.
	if (SI && result) {
		SI->Alloc(-1, (__CROWN_ADDR)result, size);
	}
	save_original_hooks();
	install_crown_hooks();
	return result;
}
#endif // MALLOC_HOOK_ENABLED

void __CrownInit(__CROWN_ID id) {
	/* read the input */
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif // MALLOC_HOOK_ENABLED
	vector<Value_t> input;
	std::ifstream in("input");
	Value_t val;
	int varType;
	char* buf = new char[128];
	while (in >>varType){
		val.type = (type_t) varType;

		if(val.type == FLOAT){
#ifdef DISABLE_FP
			assert(0 && "FP type cannot be the input value");
#endif
			in.getline(buf,20); //For newline
			in.getline(buf,128);
			val.floating = binStringToFloat(buf);	
			//		val.integral = val.floating;
		}else if(val.type == DOUBLE){
#ifdef DISABLE_FP
			assert(0 && "FP type cannot be the input value");
#endif
			in.getline(buf,20); //For newline
			in.getline(buf,128);
			val.floating = binStringToDouble(buf);
			//		val.integral = val.floating;
		}else {
			in >> val.integral;
			//		val.floating = val.integral;
		}
#ifdef DEBUG
		std::cerr<<"New Input value: "<<val.integral<<" "<< val.floating<<
			" type: "<<varType<<" input_num: "<< input.size()<<"\n";
#endif
		input.push_back(val);
	}

	in.close();
	SI = new SymbolicInterpreter(input);

	pre_symbolic = 0;

	assert(!atexit(__CrownAtExit));
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif // MALLOC_HOOK_ENABLED
}


void __CrownAtExit() {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif 
	SI->Exit();
	const SymbolicExecutionWriter& ex = SI->execution();
	const ObjectTrackerWriter* tracker = SI->tracker();
	std::ofstream out("szd_execution", std::ios::out | std::ios::binary);
	ex.Serialize(out, tracker);
	// Write symbolic objects from snapshotManager_ and arraysManager_

	assert(!out.fail());
	out.close();
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}


//
// Instrumentation functions.
//
void __CrownRegGlobal(__CROWN_ID id, __CROWN_ADDR addr, size_t size, __CROWN_TYPE ty) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
#ifdef DISABLE_FP
	if( 12 <= ty && ty <= 14){ ty = 5; } // int
#endif
	SI->Alloc(id, addr, size);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
	if (kSizeOfType[ty] == 0) return;
	for (size_t i=0; i < size / kSizeOfType[ty]; i++){
		__CROWN_VALUE val;
		__CROWN_FP_VALUE fp_val;
		switch (ty){
			case types::BOOLEAN:
				val = static_cast<bool>( *((bool *)addr+i));
				break;
			case types::U_CHAR:
				val = static_cast<unsigned char> (*((unsigned char *)addr+i));
				break;
			case types::CHAR:
				val = static_cast<char> (*((char *)addr+i));
				break;
			case types::U_SHORT:
				val = static_cast<unsigned short> (*((unsigned short *)addr+i));
				break;
			case types::SHORT:
				val = static_cast<short> (*((short *)addr+i));
				break;
			case types::U_INT:
				val = static_cast<unsigned int> (*((unsigned int *)addr+i));
				break;
			case types::INT:
				val = static_cast<int> (*((int *)addr+i));
				break;
			case types::U_LONG:
				val = static_cast<unsigned long> (*((unsigned long *)addr+i));
				break;
			case types::LONG:
				val = static_cast<long> (*((long *)addr+i));
				break;
			case types::U_LONG_LONG:
				val = static_cast<unsigned long long> (*((unsigned long long *)addr+i));
				break;
			case types::LONG_LONG:
				val = static_cast<long long> (*((long long *)addr+i));
				break;
			case types::FLOAT:
				fp_val = static_cast<float> (*((float *)addr+i));
				break;
			case types::DOUBLE:
				fp_val = static_cast<double> (*((double *)addr+i));
				break;
			case types::LONG_DOUBLE:
				fp_val = static_cast<long double> (*((long double *)addr+i));
				break;
			case types::STRUCT:
			default:
				val = 0;
				fp_val = 0;
		}

		__CrownLoad(-1, 0, 6, addr + (kSizeOfType[ty] * i), 0);
		//Last argument is for floating point
#if 0
		__CrownLoad(-1, 0, 5, i);
		__CrownPtrApply2(-1, 30, kSizeOfType[ty], addr + (kSizeOfType[ty] * i));
#endif
		__CrownLoad(-1, 0, ty, val, fp_val);
		__CrownWrite(-1, addr + (kSizeOfType[ty] * i));
	}
}

void __CrownAlloc(__CROWN_ID id, __CROWN_ADDR addr, size_t size) {
#ifdef MALLOC_HOOK_ENABLED 
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	pre_symbolic = 0;
	SI->Alloc(id, addr, size);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

void __CrownFree(__CROWN_ID id, __CROWN_ADDR addr){
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	SI->Free(id, addr);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

void __CrownLoad(__CROWN_ID id, __CROWN_ADDR addr,
		__CROWN_TYPE ty, __CROWN_VALUE val,
		__CROWN_FP_VALUE fp_val) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
#ifdef DISABLE_FP
	if( 12 <= ty && ty <= 14){ ty = 5; } // int
#endif
	if (!pre_symbolic)
		SI->Load(id, addr, Value_t(val, fp_val, static_cast<type_t>(ty)));
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

void __CrownDeref(__CROWN_ID id, __CROWN_ADDR addr,
		__CROWN_TYPE ty, __CROWN_VALUE val, __CROWN_FP_VALUE fp_val) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
#ifdef DISABLE_FP
	if( 12 <= ty && ty <= 14){ ty = 5; } // int
#endif
	if (!pre_symbolic)
		SI->Deref(id, addr, Value_t(val, fp_val, static_cast<type_t>(ty)));
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

void __CrownStore(__CROWN_ID id, __CROWN_ADDR addr) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	if (!pre_symbolic)
		SI->Store(id, addr);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

void __CrownWrite(__CROWN_ID id, __CROWN_ADDR addr) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	if (!pre_symbolic)
		SI->Write(id, addr);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

void __CrownClearStack(__CROWN_ID id) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	if (!pre_symbolic)
		SI->ClearStack(id);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}


void __CrownApply1(__CROWN_ID id, __CROWN_OP op,
		__CROWN_TYPE ty, __CROWN_VALUE val, 
		__CROWN_FP_VALUE fp_val) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	assert((op >= __CROWN_NEGATE) && (op <= __CROWN_S_CAST));

#ifdef DISABLE_FP
	if( 12 <= ty && ty <= 14){ ty = 5; } // int
#endif

	if (!pre_symbolic)
		SI->ApplyUnaryOp(id,
				static_cast<unary_op_t>(kOpTable[op]),
				Value_t(val,fp_val,static_cast<type_t>(ty)));
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}


void __CrownApply2(__CROWN_ID id, __CROWN_OP op,
		__CROWN_TYPE ty, __CROWN_VALUE val,
		__CROWN_FP_VALUE fp_val) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	assert((op >= __CROWN_ADD) && (op <= __CROWN_CONCRETE));

#ifdef DISABLE_FP
	if( 12 <= ty && ty <= 14){ ty = 5; } // int
#endif

	if (pre_symbolic)
		return;

	if ((op >= __CROWN_EQ) && (op <= __CROWN_S_GEQ)) {
		SI->ApplyCompareOp(id,
				static_cast<compare_op_t>(kOpTable[op]),
				Value_t(val,fp_val,static_cast<type_t>(ty)));
	} else {
		SI->ApplyBinaryOp(id,
				static_cast<binary_op_t>(kOpTable[op]),
				Value_t(val,fp_val,static_cast<type_t>(ty)));
	}
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

void __CrownPtrApply2(__CROWN_ID id, __CROWN_OP op,
		size_t size, __CROWN_VALUE val) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	if (pre_symbolic)
		return;
	SI->ApplyBinPtrOp(id, static_cast<pointer_op_t>(kOpTable[op]), size, val);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

void __CrownBranch(__CROWN_ID id, __CROWN_BRANCH_ID bid, __CROWN_BOOL b,
		__CROWN_LINE_NO l, __CROWN_FILE_NAME f, __CROWN_EXP e) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	if (pre_symbolic) {
		// Precede the branch with a fake (concrete) load.
		SI->Load(id, 0, Value_t(b, b, types::CHAR));
	}
    /*
     * written by Hyunwoo Kim (17.07.13)
     * the line number information was refined to exact value.
     */
	SI->Branch(id, bid, static_cast<bool>(b), l-1, f, e);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}


void __CrownCall(__CROWN_ID id, __CROWN_FUNCTION_ID fid) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif

    if (!enable_symbolic) return;
	SI->Call(id, fid);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}


void __CrownReturn(__CROWN_ID id) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
    if (!enable_symbolic) return;
	SI->Return(id);
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}


void __CrownHandleReturn(__CROWN_ID id, __CROWN_TYPE ty, __CROWN_VALUE val, __CROWN_FP_VALUE fp_val) {
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
#ifdef DISABLE_FP
	if( 12 <= ty && ty <= 14){ ty = 5; } // int
#endif
    if (!enable_symbolic) return;
	if (!pre_symbolic)
		SI->HandleReturn(id, Value_t(val, fp_val, static_cast<type_t>(ty)));
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}


/*
 * Symbolic input functions.
 *
 * comments written by Hyunwoo Kim (17.07.13)
 * additional parameters, the name of symbolic variable,
 * its declared line and file name were added.
 */

void __CrownUChar(unsigned char* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;	
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (unsigned char)SI->NewInput(types::U_CHAR, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownUChar2() -> __CrownUCharInit()
void __CrownUCharInit(unsigned char* x, unsigned char val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::U_CHAR);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (unsigned char)SI->NewInput2(types::U_CHAR, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}

void __CrownUShort(unsigned short* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (unsigned short)SI->NewInput(types::U_SHORT, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownUShort2() -> __CrownUShortInit()
void __CrownUShortInit(unsigned short* x, unsigned short val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::U_SHORT);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (unsigned short)SI->NewInput2(types::U_SHORT, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownUInt(unsigned int* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (unsigned int)SI->NewInput(types::U_INT, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownUInt2() -> __CrownUIntInit()
void __CrownUIntInit(unsigned int* x, unsigned int val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::U_INT);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (unsigned int)SI->NewInput2(types::U_INT, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownULong(unsigned long* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (unsigned long)SI->NewInput(types::U_LONG, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownULong2() -> __CrownULongInit()
void __CrownULongInit(unsigned long* x, unsigned long val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::U_LONG);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (unsigned long)SI->NewInput2(types::U_LONG, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownULongLong(unsigned long long* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (unsigned long long)SI->NewInput(types::U_LONG_LONG, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownULongLong2() -> __CrownULongLongInit()
void __CrownULongLongInit(unsigned long long* x, unsigned long long val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::U_LONG_LONG);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (unsigned long long)SI->NewInput2(types::U_LONG_LONG, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownChar(char* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;
	
	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (char)SI->NewInput(types::CHAR, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownChar2() -> __CrownCharInit()
void __CrownCharInit(char* x, char val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::CHAR);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (char)SI->NewInput2(types::CHAR, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownShort(short* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (short)SI->NewInput(types::SHORT, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownShort2() -> __CrownShortInit()
void __CrownShortInit(short* x, short val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::SHORT);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (short)SI->NewInput2(types::SHORT, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownInt(int* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (int)SI->NewInput(types::INT, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownInt2() -> __CrownIntInit()
void __CrownIntInit(int* x, int val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::INT);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (int)SI->NewInput2(types::INT, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownLong(long* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (long)SI->NewInput(types::LONG, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownLong2() -> __CrownLongInit()
void __CrownLongInit(long* x, long val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::LONG);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (long)SI->NewInput2(types::LONG, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownLongLong(long long* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (long long)SI->NewInput(types::LONG_LONG, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownLongLong2() -> __CrownLongLongInit()
void __CrownLongLongInit(long long* x, long long val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(val, 0, types::LONG_LONG);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (long long)SI->NewInput2(types::LONG_LONG, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownFloat(float* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif

#ifdef DISABLE_FP
	assert(0 && "FP type is disabled");
#endif

	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (float)SI->NewInput(types::FLOAT, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).floating;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownFloat2() -> __CrownFloatInit()
void __CrownFloatInit(float* x, float val,  int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(0, val, types::FLOAT);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
#ifdef DISABLE_FP
    assert(0 && "FP type is disabled");
#endif

    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (float)SI->NewInput2(types::FLOAT, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).floating;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownDouble(double* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
#ifdef DISABLE_FP
	assert(0 && "FP type is disabled");
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (double)SI->NewInput(types::DOUBLE, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).floating;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownDouble2() -> __CrownDoubleInit()
void __CrownDoubleInit(double* x, double val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(0, val, types::DOUBLE);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
#ifdef DISABLE_FP
    assert(0 && "FP type is disabled");
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (double)SI->NewInput2(types::DOUBLE, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).floating;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownLongDouble(long double* x, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
#ifdef DISABLE_FP
	assert(0 && "FP type is disabled");
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (long double)SI->NewInput(types::LONG_DOUBLE, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).floating;
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}

// Kunwoo Park (2018-11-09) : Renaming __CrownLongDouble2() -> __CrownLongDoubleInit()
void __CrownLongDoubleInit(long double* x, long double val, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
    Value_t init_val(0, val, types::LONG_DOUBLE);
#ifdef MALLOC_HOOK_ENABLED
    restore_original_hooks();
#endif
#ifdef DISABLE_FP
    assert(0 && "FP type is disabled");
#endif
    pre_symbolic = 0;

    std::stringstream sym_name;
    sym_name << var_name << "_" << cnt_sym_var;
    *x = (long double)SI->NewInput2(types::LONG_DOUBLE, (addr_t)x, init_val, const_cast<char *>(sym_name.str().c_str()), ln, fname).floating;
#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
    install_crown_hooks();
#endif
}


void __CrownPointer(void ** x, value_t size, int cnt_sym_var, int ln, char* fname, ...) {
    va_list ap;
    va_start(ap, fname);
    char* var_name = va_arg(ap, char*);
    va_end(ap);
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;
	sym_name << var_name << "_" << cnt_sym_var;
	*x = (void *)SI->NewInput(types::POINTER, (addr_t)x, const_cast<char *>(sym_name.str().c_str()), ln, fname).integral;

	if (*x != NULL){
		void *newAddr = AddrMap[*x];
		if (newAddr == NULL){
			newAddr = malloc(size);
			AddrMap[*x] = newAddr;
		}
		*x = newAddr;
	}
#ifdef MALLOC_HOOK_ENABLED
	save_original_hooks();
	install_crown_hooks();
#endif
}


unsigned long long __CrownBitField(unsigned char* x, char unionSize, int lowestBit, int highestBit, int cnt_sym_var, int ln, char* fname, ...) {
	va_list ap;
  va_start(ap, fname);
  char* var_name = va_arg(ap, char*);
  va_end(ap);

	unsigned char lowestIndex = lowestBit / 8;
	unsigned char highestIndex = (highestBit%8 == 0) ? (highestBit / 8 - 1) : (highestBit / 8);
	int indexSize = highestIndex - lowestIndex + 1;
	unsigned char h = ((highestBit - 1) % 8) + 1;
	unsigned char l = (lowestBit % 8);
	char i;
#ifdef MALLOC_HOOK_ENABLED
	restore_original_hooks();
#endif
	pre_symbolic = 0;

	std::stringstream sym_name;	
	sym_name << var_name << "_" << cnt_sym_var;

	if (unionSize == 0) {//is struct
			if(lowestIndex == highestIndex){
				unsigned char oldValue = *(x + lowestIndex);
				std::stringstream sym_index_name;
				sym_index_name << var_name << "[" << (int) lowestIndex << "]_" << cnt_sym_var;
				*(x+lowestIndex) = (unsigned char)SI->NewInput( types::BITFIELD_CHAR , (addr_t)x+lowestIndex, const_cast<char *>(sym_index_name.str().c_str()), ln, fname, oldValue,h,l,1).integral;
			} else {

				unsigned char oldValue = *(x+ lowestIndex);
				std::stringstream sym_index_name;
				sym_index_name << var_name << "[" << (int) lowestIndex <<  "]_" << cnt_sym_var;
				*(x+lowestIndex) = (unsigned char)SI->NewInput( types::BITFIELD_CHAR, (addr_t)x+lowestIndex , const_cast<char *>(sym_index_name.str().c_str()), ln, fname, oldValue, 8, l,indexSize).integral;
				for ( i = lowestIndex + 1; i < highestIndex; i ++){
					std::stringstream sym_index_name_;
					sym_index_name_ << var_name << "[" << (int) i << "]_" << cnt_sym_var;
					*(x + i) = (unsigned char) SI->NewInput(types::U_CHAR, (addr_t) x+i, const_cast<char *>(sym_index_name_.str().c_str()),ln,fname).integral;
				}
				std::stringstream sym_index_name1;
				sym_index_name1 << var_name << "[" << (int) highestIndex <<  "]_" << cnt_sym_var;
				oldValue = *(x+highestIndex);
				*(x + highestIndex) = (unsigned char) SI->NewInput(types::BITFIELD_CHAR, (addr_t)x+highestIndex, const_cast<char *>(sym_index_name1.str().c_str()), ln, fname, oldValue,h,0, indexSize).integral;
			}
	} else {
			if (unionSize == 1){
					unsigned char oldValue = *x;
					*x = (unsigned char) SI->NewInput(types::BITFIELD_CHAR, (addr_t)x, const_cast<char *> (sym_name.str().c_str()), ln, fname, oldValue,h,l,0).integral;
			} else if (unionSize == 2){
					unsigned short * cast_x = (unsigned short *) x;
					unsigned short oldValue = *(cast_x);
					*cast_x = (unsigned short) SI->NewInput (types::BITFIELD_UNION_SHORT, (addr_t)x, const_cast<char *> (sym_name.str().c_str()), ln, fname, oldValue,h,l,0).integral;
			} else if (unionSize == 4){
					unsigned int * cast_x = (unsigned int *) x;
					unsigned int oldValue = *(cast_x);
					*cast_x = (unsigned int) SI-> NewInput(types::BITFIELD_UNION_INT, (addr_t)x, const_cast<char *> (sym_name.str().c_str()), ln, fname, oldValue,h,l,0).integral;
			} else if (unionSize == 8) {
					unsigned long long * cast_x = (unsigned long long *) x;
					unsigned long long oldValue = *(cast_x);
					*cast_x = (unsigned long long) SI-> NewInput(types::BITFIELD_UNION_LONGLONG, (addr_t)x, const_cast<char*> (sym_name.str().c_str()), ln,fname, oldValue,h,l,0).integral;
			}

	}

#ifdef MALLOC_HOOK_ENABLED
    save_original_hooks();
	install_crown_hooks();
#endif
	return 0;
}

void __CrownSetCallerCalleeName(__CROWN_ID id, char *caller_, char *callee_){
    if (!enable_symbolic) return;
    assert(caller_);
    assert(callee_);
    strncpy(caller, caller_, sizeof(caller));
    strncpy(callee, callee_, sizeof(callee));
}
void __CrownEnableSymbolic(__CROWN_ID id, char *caller_){
    // XXX: Recursion may corrupt this feature
    // especilly when the caller of disabler is 
    // called recursively by the uninstrumented function.
    if (strcmp(caller, caller_) == 0){
        enable_symbolic = 1;
    }
}
void __CrownCheckSymbolic (__CROWN_ID id, char *callee_){
    if (!enable_symbolic) return;
    // Ignore main() func
    // XXX: assume that main is not called recursively
    if (strcmp(callee_, "main") == 0) return; 
    if (strcmp(callee, callee_) != 0){
        enable_symbolic = 0;
    }
}   
