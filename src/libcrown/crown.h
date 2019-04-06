/* Copyright (c) 2015-2018, Software Testing & Verification Group
 *
 * This file is part of CROWN, which is distributed under the revised
 * BSD license.  A copy of this license can be found in the file LICENSE.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
 * for details.
 */

#ifndef LIBCROWN_CROWN_H__
#define LIBCROWN_CROWN_H__

#define FILE2SHOW_ASSUME_VIOLATED "__SYM_assume_violated"

#include <stdlib.h>
#include <stdio.h>

/*
 * During instrumentation, the folowing function calls are inserted in the
 * C code under test.
 *
 * These calls (loosely) correspond to an execution of the program
 * under test by a stack machine.  It is intended that these calls be
 * used to symbolically execute the program under test, by maintaining
 * a a symbolic stack (along with a symbolic memory map).  Specifically:
 *
 *  - A C expression (with no side effects) generates a series of Load
 *    and Apply calls corresponding to the "postfix" evaluation of the
 *    expression, using a stack (i.e. a Load indicates that a value is
 *    pushed onto the stack, and unary and binary operations are applied
 *    to one/two values popped off the stack).  For example, the expression
 *    "a*b > 3+c" would generate the instrumentation:
 *        Load(&a, a)
 *        Load(&b, b)
 *        ApplyBinOp(MULTIPLY, a*b)
 *        Load(0, 3)
 *        Load(&c, c)
 *        ApplyBinOp(ADD, 3+c)
 *        ApplyBinOp(GREATER_THAN, a*b > 3+c)
 *    Note that each Load and Apply call includes the concrete value either
 *    loaded or computed.  Also note that constants are treated as having
 *    address "0".
 *
 * - Entering the then- or else-block of an if statement generates a Branch
 *   call indicating which branch was taken.  The branch is on the value
 *   popped from the stack.  For example, "if (a*b > 3+c) ..." generates
 *   the series of Load and Apply calls above, plus one of:
 *       Branch(true_id,  1)
 *       Branch(false_id, 0)
 *
 * - An assignment statement generates a single Store call, indicating
 *   that a value is popped off the stack and stored in the given address.
 *   For example, "a = 3 + b" generates:
 *        Load(0, 3)
 *        Load(&b, b)
 *        ApplyBinOp(ADD, 3+b)
 *        Store(&a)
 *
 * - The instrumentation for function calls is somewhat complicated,
 *   because we have to handle the case where an instrumented code
 *   calls an un-instrumented function.  (We currently forbid
 *   un-instrumented code from calling back into instrumented code.)
 *
 *   * For all calls, the actual function arguments are pushed onto
 *     the stack.  In the body of the called function (if
 *     instrumented), these values are Stored in the formal
 *     parameters.  (See example below.)
 *
 *   * In the body of the called function, "return e" generates the
 *     instrumentation for expression "e", followed by a call to
 *     Return.  An void "return" statement similary generates a call
 *     to Return.
 *
 *   * If the returned value is assigned to some variable -- e.g.
 *     "z = max(a, 7)" -- then two calls are generated:
 *         HandleReturn([concrete returned value])
 *         Store(&z)
 *     If, instead, the return value is ignored -- e.g. "max(a, 7);"
 *     -- a single call to ClearStack is generated.

 *     [The difficultly here is that, if the called function was not
 *      instrumented, HandleReturn must clean up the stack -- which
 *      will still contain the arguments to the function -- and then
 *      load the concrete returned value onto the stack to then be
 *      stored.  If the called function is instrumented, then HandleReturn
 *      need not modify the stack -- it already contains a single element
 *      (the returned value).]
 *
 *    * Full example:  Consider the function "add(x, y) { return x+y; }".
 *      A call "z = add(a, 7)" generates instrumentation calls:
 *          Load(&a, a)
 *          Load(0, 7)
 *          Call(add)
 *          Store(&y)
 *          Store(&x)
 *          Load(&x, x)
 *          Load(&y, y)
 *          ApplyBinOp(ADD, x+y)
 *          Return()
 *          HandleReturn(z)
 *          Store(&z)
 *
 * - A symbolic input generates a call to create a new symbol (passing
 *   the conrete initial value for that symbol).
 *
 *   [We pass the conrete value and have signed/unsigned versions only
 *   to make it easier to exactly capture/print the concrete inputs to
 *   the program under test.]
 *
 * - When loading and storing structs, arrays, unions, or other
 *   aggregates (the only operations that can be performed on
 *   aggregates), the type is __CROWN_STRUCT and the value is the
 *   size of the aggregate in bytes.
 *
 */

#ifdef __cplusplus
#define EXTERN extern "C"
#else
#define EXTERN extern
#endif

/*
 * Type definitions.
 *
 * These macros must be kept in sync with the definitions in base/basic_types.h.
 * We use these obscure MACRO's rather than the definitions in basic_types.h
 * in an attempt to avoid clashing with names in instrumented programs
 * (and also because C does not support namespaces).
 */
#define __CROWN_ID int
#define __CROWN_BRANCH_ID int
#define __CROWN_FUNCTION_ID unsigned int
#define __CROWN_VALUE long long int
#define __CROWN_FP_VALUE double
#define __CROWN_ADDR unsigned long int

#define __CROWN_OP int
#define __CROWN_TYPE int
#define __CROWN_BOOL unsigned char

#define __CROWN_LINE_NO unsigned int
#define __CROWN_FILE_NAME const char*
#define __CROWN_EXP const char*

/*
 * Constants representing possible C operators.
 */
enum {
	/* binary arithmetic */
	__CROWN_ADD        =  0,
	__CROWN_SUBTRACT   =  1,
	__CROWN_MULTIPLY   =  2,
	__CROWN_DIVIDE     =  3,
	__CROWN_S_DIVIDE   =  4,
	__CROWN_MOD        =  5,
	__CROWN_S_MOD      =  6,
	/* binary bitwise operators */
	__CROWN_SHIFT_L    =  7,
	__CROWN_SHIFT_R    =  8,
	__CROWN_S_SHIFT_R  =  9,
	__CROWN_AND        = 10,
	__CROWN_OR         = 11,
	__CROWN_XOR        = 12,
	/* binary comparison */
	__CROWN_EQ         = 13,
	__CROWN_NEQ        = 14,
	__CROWN_GT         = 15,
	__CROWN_S_GT       = 16,
	__CROWN_LEQ        = 17,
	__CROWN_S_LEQ      = 18,
	__CROWN_LT         = 19,
	__CROWN_S_LT       = 20,
	__CROWN_GEQ        = 21,
	__CROWN_S_GEQ      = 22,
	/* unhandled binary operators */
	__CROWN_CONCRETE   = 23,
	/* unary operators */
	__CROWN_NEGATE     = 24,
	__CROWN_NOT        = 25,
	__CROWN_L_NOT      = 26,
	/* cast */
	__CROWN_CAST       = 27,
	__CROWN_S_CAST     = 28,
	/* pointer ops */
	__CROWN_ADD_PI     = 29,
	__CROWN_S_ADD_PI   = 30,
	__CROWN_SUB_PI     = 31,
	__CROWN_S_SUB_PI   = 32,
	__CROWN_SUB_PP     = 33,
};

enum {
	__CROWN_U_CHAR = 0,       __CROWN_CHAR = 1,
	__CROWN_U_SHORT = 2,      __CROWN_SHORT = 3,
	__CROWN_U_INT = 4,        __CROWN_INT = 5,
	__CROWN_U_LONG = 6,       __CROWN_LONG = 7,
	__CROWN_U_LONG_LONG = 8,  __CROWN_LONG_LONG = 9,
	__CROWN_STRUCT = 10,		__CROWN_POINTER = 11,
	__CROWN_FLOAT = 12,
	__CROWN_DOUBLE = 13, 		__CROWN_LONG_DOUBLE = 14,
};

/*
 * Short-cut to indicate that a function should be skipped during
 * instrumentation.
 */
#define __SKIP __attribute__((crown_skip))

/*
 * Instrumentation functions.
 *
 * (Could also clone these for each type: uint8, int8, ..., uint64, int64.)
 */
EXTERN void __CrownInit(__CROWN_ID) __SKIP;
EXTERN void __CrownRegGlobal(__CROWN_ID, __CROWN_ADDR, unsigned long, __CROWN_TYPE) __SKIP;
EXTERN void __CrownAlloc(__CROWN_ID, __CROWN_ADDR, unsigned long) __SKIP;
EXTERN void __CrownFree(__CROWN_ID, __CROWN_ADDR) __SKIP;
EXTERN void __CrownLoad(__CROWN_ID, __CROWN_ADDR, __CROWN_TYPE, __CROWN_VALUE, __CROWN_FP_VALUE) __SKIP;
EXTERN void __CrownDeref(__CROWN_ID, __CROWN_ADDR, __CROWN_TYPE, __CROWN_VALUE, __CROWN_FP_VALUE) __SKIP;
EXTERN void __CrownStore(__CROWN_ID, __CROWN_ADDR) __SKIP;
EXTERN void __CrownWrite(__CROWN_ID, __CROWN_ADDR) __SKIP;
EXTERN void __CrownClearStack(__CROWN_ID) __SKIP;
EXTERN void __CrownApply1(__CROWN_ID, __CROWN_OP, __CROWN_TYPE, __CROWN_VALUE, __CROWN_FP_VALUE) __SKIP;
EXTERN void __CrownApply2(__CROWN_ID, __CROWN_OP, __CROWN_TYPE, __CROWN_VALUE, __CROWN_FP_VALUE) __SKIP;
EXTERN void __CrownPtrApply2(__CROWN_ID, __CROWN_OP, unsigned long, __CROWN_VALUE) __SKIP;
EXTERN void __CrownBranch(__CROWN_ID, __CROWN_BRANCH_ID, __CROWN_BOOL, __CROWN_LINE_NO, __CROWN_FILE_NAME, __CROWN_EXP) __SKIP;
EXTERN void __CrownCall(__CROWN_ID, __CROWN_FUNCTION_ID) __SKIP;
EXTERN void __CrownReturn(__CROWN_ID) __SKIP;
EXTERN void __CrownHandleReturn(__CROWN_ID,  __CROWN_TYPE, __CROWN_VALUE, __CROWN_FP_VALUE) __SKIP;
EXTERN void __CrownSetCallerCalleeName(__CROWN_ID, char *caller, char *callee) __SKIP;
EXTERN void __CrownEnableSymbolic(__CROWN_ID, char *caller) __SKIP;
EXTERN void __CrownCheckSymbolic(__CROWN_ID, char *callee) __SKIP;
  /* Kunwoo Park (2018-11-09) : Define SYM_assume()            *
   * Input: Boolean Expression                                 *
   * If input expression is not satisfied,                     *
   * 1. Prints an error message                                *
   * 2. Generates a file to communicate with run_crown process *
   * 3. Exit the current process                               */
#define SYM_assume(e) \
do { \
  if (!(e)) { \
    fprintf(stderr, "### SYM_assume(%s) is violated at Line %d (%s in %s) ###\n", #e, __LINE__, __FUNCTION__, __FILE__); \
    FILE * f = fopen( FILE2SHOW_ASSUME_VIOLATED, "w"); \
    if(!f) fprintf(stderr,"### %s file cannot be created ###\n", FILE2SHOW_ASSUME_VIOLATED); \
    else fclose(f); \
    exit(1); \
  } } while (0) 

/*
 * Functions (macros) for obtaining symbolic inputs.
 * comments written by Hyunwoo Kim (17.07.13)
 * symbolic declaration macro function has 2 additional parameters to pass
 * the information for the line and file name of declaration using
 * __LINE__, __FILE__ directive.
 *
 * Optionally, it has 1 more paramter for symbolic variable name
 * (if the user describes it, 2nd paratmter,  in macro function
 * like SYM_int(a, "sym_a") )

 *
 * the variable cnt_symbolic_var is used to save the # of occurrence
 * of same symbolic variable.
 * e.g)
 * int a;
 * for (int i=0;i<10;i++)
 *      SYM_int(a);
 * Here, multiple symbolic declaration occurs and the # of
 * occurence is printed in path condition.
 */


#ifdef CIL
#define SYM_unsigned_char(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUChar(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUChar(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	        cnt_symbolic_var++; }
#define SYM_unsigned_short(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUShort(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUShort(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_unsigned_int(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUInt(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUInt(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_unsigned_long(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULong(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULong(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_unsigned_longlong(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULongLong(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULongLong(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_char(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownChar(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownChar(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_short(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownShort(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownShort(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_int(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownInt(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownInt(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_long(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLong(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLong(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_longlong(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongLong(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongLong(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_float(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownFloat(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownFloat(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_double(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownDouble(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownDouble(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_longdouble(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongDouble(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongDouble(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_pointer(x, size, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownPointer(&x, size, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUChar(&x, size, cnt_symbolic_var, __LINE__, __FILE__, #x); \
	            cnt_symbolic_var++; }
#define SYM_bitfield(x, ...) { static int cnt_symbolic_var = 1; \
	        (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? (x = __CrownBitField(x,0,0,0, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__))  : (x = __CrownBitField(x, 0,0,0,cnt_symbolic_var, __LINE__, __FILE__, #x)); \
	            cnt_symbolic_var++; }

#define SYM_unsigned_char_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUChar(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUChar(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
              cnt_symbolic_var++; }
#define SYM_unsigned_short_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUShort(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUShort(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_unsigned_int_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUInt(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUInt(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_unsigned_long_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULong(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULong(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_unsigned_longlong_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULongLong(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULongLong(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_char_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownChar(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownChar(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_short_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownShort(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownShort(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_int_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownInt(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownInt(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_long_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLong(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLong(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_longlong_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongLong(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongLong(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_float_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownFloat(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownFloat(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_double_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownDouble(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownDouble(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_longdouble_bit(x, ...) { static int cnt_symbolic_var = 1; \
              (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongDouble(&x, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongDouble(&x, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }


#define SYM_is_fresh(x) __CrownIsFresh(&x)

#define VA_NUM_ARGS_IMPL(_1, _2, N, ...) N
/* Kunwoo Park (2018-11-09)                                               *
 * 1. Renaming SYM_unsigned_char_2() -> SYM_unsigned_char_init() and etc. *
 * 2. Renaming __CrownUChar2() -> __CrownUCharInit() and etc.             */
#define SYM_unsigned_char_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUCharInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUCharInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
            cnt_symbolic_var++; }
#define SYM_unsigned_short_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUShortInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUShortInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_unsigned_int_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUIntInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUIntInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_unsigned_long_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULongInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULongInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_unsigned_long_long_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULongLongInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULongLongInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_char_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownCharInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownCharInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_short_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownShortInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownShortInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_int_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownIntInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownIntInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_long_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_long_long_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongLongInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongLongInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_float_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownFloatInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownFloatInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_double_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownDoubleInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownDoubleInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_long_double_init(x, val, ...) { static int cnt_symbolic_var = 1; \
            (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongDoubleInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongDoubleInit(&x, val, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }

EXTERN void __CrownUChar(unsigned char* x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownUShort(unsigned short* x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownUInt(unsigned int* x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownULong(unsigned long* x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownULongLong(unsigned long long* x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownChar(char* x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownShort(short* x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownInt(int* x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownLong(long * x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownLongLong(long long * x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownFloat(float * x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownDouble(double * x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownLongDouble(long double * x, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownPointer(void ** x, __CROWN_VALUE, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN int __CrownIsFresh(void ** x) __SKIP;
EXTERN unsigned long long __CrownBitField(unsigned char* x,char unionSize, int lowestBit, int highestBit, int cnt_sym_var, int ln, char* fname, ...);
// Kunwoo Park (2018-11-09) : Renaming __CrownUChar2() -> __CrownUCharInit() and etc.
EXTERN void __CrownUCharInit(unsigned char* x, unsigned char val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownUShortInit(unsigned short* x, unsigned short val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownUIntInit(unsigned int* x, unsigned int val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownULongInit(unsigned long* x, unsigned long val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownULongLongInit(unsigned long long* x, unsigned long long val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownCharInit(char* x, char val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownShortInit(short* x, short val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownIntInit(int* x, int val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownLongInit(long * x, long val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownLongLongInit(long long * x, long long val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownFloatInit(float * x, float val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownDoubleInit(double * x, double val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void __CrownLongDoubleInit(long double * x, long double val, int cnt_sym_var, int ln, char* fname, ...) __SKIP;

#else
#define SYM_unsigned_char_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUChar(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUChar(cnt_symbolic_var, __LINE__, __FILE__, #x); \
              cnt_symbolic_var++; }
#define SYM_unsigned_short_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUShort(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUShort(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_unsigned_int_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUInt(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUInt(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_unsigned_long_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULong(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULong(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_unsigned_longlong_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULongLong(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULongLong(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_char_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownChar(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownChar(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_short_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownShort(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownShort(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_int_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownInt(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownInt(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_long_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLong(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLong(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_longlong_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongLong(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongLong(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_float_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownFloat(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownFloat(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_double_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownDouble(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownDouble(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }
#define SYM_longdouble_bit(x, ...) { static int cnt_symbolic_var = 1; \
              x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongDouble(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongDouble(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                  cnt_symbolic_var++; }

#define SYM_unsigned_char(x, ...) { static int cnt_symbolic_var = 1; \
                *(unsigned char *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUChar(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUChar(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                cnt_symbolic_var++; }
#define SYM_unsigned_short(x, ...) { static int cnt_symbolic_var = 1; \
                *(unsigned short *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUShort(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUShort(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_unsigned_int(x, ...) { static int cnt_symbolic_var = 1; \
                *(unsigned int *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownUInt(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUInt(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_unsigned_long(x, ...) { static int cnt_symbolic_var = 1; \
                *(unsigned long *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULong(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULong(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_unsigned_longlong(x, ...) { static int cnt_symbolic_var = 1; \
                *(unsigned long long *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownULongLong(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownULongLong(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_char(x, ...) { static int cnt_symbolic_var = 1; \
                *(char *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownChar(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownChar(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_short(x, ...) { static int cnt_symbolic_var = 1; \
                *(short *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownShort(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownShort(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_int(x, ...) { static int cnt_symbolic_var = 1; \
                *(int *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownInt(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownInt(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_long(x, ...) { static int cnt_symbolic_var = 1; \
                *(long *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLong(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLong(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_longlong(x, ...) { static int cnt_symbolic_var = 1; \
                *(long long *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongLong(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongLong(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_float(x, ...) { static int cnt_symbolic_var = 1; \
                *(float *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownFloat(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownFloat(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_double(x, ...) { static int cnt_symbolic_var = 1; \
                *(double *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownDouble(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownDouble(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_longdouble(x, ...) { static int cnt_symbolic_var = 1; \
                *(long double *)&x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownLongDouble(cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownLongDouble(cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_pointer(x, size, ...) { static int cnt_symbolic_var = 1; \
                x = (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? __CrownPointer(size, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__)  : __CrownUChar(size, cnt_symbolic_var, __LINE__, __FILE__, #x); \
                    cnt_symbolic_var++; }
#define SYM_bitfield(x, ...) { static int cnt_symbolic_var = 1; \
                (VA_NUM_ARGS_IMPL(0,## __VA_ARGS__, 1, 0)) ? (x = __CrownBitField(x,0,0,0, cnt_symbolic_var, __LINE__, __FILE__,## __VA_ARGS__))  : (x = __CrownBitField(x, 0,0,0,cnt_symbolic_var, __LINE__, __FILE__, #x)); \
                    cnt_symbolic_var++; }

#define SYM_is_fresh(x) __CrownIsFresh(&x)

#define VA_NUM_ARGS_IMPL(_1, _2, N, ...) N

EXTERN unsigned char __CrownUChar(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN unsigned short __CrownUShort(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN unsigned int __CrownUInt(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN unsigned long __CrownULong(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN unsigned long long __CrownULongLong(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN char __CrownChar(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN short __CrownShort(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN int __CrownInt(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN long __CrownLong(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN long long __CrownLongLong(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN float __CrownFloat(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN double __CrownDouble(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN long double __CrownLongDouble(int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN void * __CrownPointer(__CROWN_VALUE, int cnt_sym_var, int ln, char* fname, ...) __SKIP;
EXTERN int __CrownIsFresh(void ** x) __SKIP;
EXTERN unsigned long long __CrownBitField(unsigned char* x,char unionSize, int lowestBit, int highestBit, int cnt_sym_var, int ln, char* fname, ...);


#endif
#endif  /* LIBCROWN_CROWN_H__ */
