/* 
 * CS:APP Data Lab 
 * 
 * <Please put your name and userid here>
 * 
 * bits.c - Source file with your solutions to the Lab.
 *          This is the file you will hand in to your instructor.
 *
 * WARNING: Do not include the <stdio.h> header; it confuses the dlc
 * compiler. You can still use printf for debugging without including
 * <stdio.h>, although you might get a compiler warning. In general,
 * it's not good practice to ignore compiler warnings, but in this
 * case it's OK.  
 */

#if 0
/*
 * Instructions to Students:
 *
 * STEP 1: Read the following instructions carefully.
 */

You will provide your solution to the Data Lab by
editing the collection of functions in this source file.

INTEGER CODING RULES:
 
  Replace the "return" statement in each function with one
  or more lines of C code that implements the function. Your code 
  must conform to the following style:
 
  int Funct(arg1, arg2, ...) {
      /* brief description of how your implementation works */
      int var1 = Expr1;
      ...
      int varM = ExprM;

      varJ = ExprJ;
      ...
      varN = ExprN;
      return ExprR;
  }

  Each "Expr" is an expression using ONLY the following:
  1. Integer constants 0 through 255 (0xFF), inclusive. You are
      not allowed to use big constants such as 0xffffffff.
  2. Function arguments and local variables (no global variables).
  3. Unary integer operations ! ~
  4. Binary integer operations & ^ | + << >>
    
  Some of the problems restrict the set of allowed operators even further.
  Each "Expr" may consist of multiple operators. You are not restricted to
  one operator per line.

  You are expressly forbidden to:
  1. Use any control constructs such as if, do, while, for, switch, etc.
  2. Define or use any macros.
  3. Define any additional functions in this file.
  4. Call any functions.
  5. Use any other operations, such as &&, ||, -, or ?:
  6. Use any form of casting.
  7. Use any data type other than int.  This implies that you
     cannot use arrays, structs, or unions.

 
  You may assume that your machine:
  1. Uses 2s complement, 32-bit representations of integers.
  2. Performs right shifts arithmetically.
  3. Has unpredictable behavior when shifting if the shift amount
     is less than 0 or greater than 31.


EXAMPLES OF ACCEPTABLE CODING STYLE:
  /*
   * pow2plus1 - returns 2^x + 1, where 0 <= x <= 31
   */
  int pow2plus1(int x) {
     /* exploit ability of shifts to compute powers of 2 */
     return (1 << x) + 1;
  }

  /*
   * pow2plus4 - returns 2^x + 4, where 0 <= x <= 31
   */
  int pow2plus4(int x) {
     /* exploit ability of shifts to compute powers of 2 */
     int result = (1 << x);
     result += 4;
     return result;
  }

FLOATING POINT CODING RULES

For the problems that require you to implement floating-point operations,
the coding rules are less strict.  You are allowed to use looping and
conditional control.  You are allowed to use both ints and unsigneds.
You can use arbitrary integer and unsigned constants. You can use any arithmetic,
logical, or comparison operations on int or unsigned data.

You are expressly forbidden to:
  1. Define or use any macros.
  2. Define any additional functions in this file.
  3. Call any functions.
  4. Use any form of casting.
  5. Use any data type other than int or unsigned.  This means that you
     cannot use arrays, structs, or unions.
  6. Use any floating point data types, operations, or constants.


NOTES:
  1. Use the dlc (data lab checker) compiler (described in the handout) to 
     check the legality of your solutions.
  2. Each function has a maximum number of operations (integer, logical,
     or comparison) that you are allowed to use for your implementation
     of the function.  The max operator count is checked by dlc.
     Note that assignment ('=') is not counted; you may use as many of
     these as you want without penalty.
  3. Use the btest test harness to check your functions for correctness.
  4. Use the BDD checker to formally verify your functions
  5. The maximum number of ops for each function is given in the
     header comment for each function. If there are any inconsistencies 
     between the maximum ops in the writeup and in this file, consider
     this file the authoritative source.

/*
 * STEP 2: Modify the following functions according the coding rules.
 * 
 *   IMPORTANT. TO AVOID GRADING SURPRISES:
 *   1. Use the dlc compiler to check that your solutions conform
 *      to the coding rules.
 *   2. Use the BDD checker to formally verify that your solutions produce 
 *      the correct answers.
 */

#endif
/* Copyright (C) 1991-2020 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */
/* This header is separate from features.h so that the compiler can
   include it implicitly at the start of every compilation.  It must
   not itself include <features.h> or any other header that includes
   <features.h> because the implicit include comes before any feature
   test macros that may be defined in a source file before it first
   explicitly includes a system header.  GCC knows the name of this
   header in order to preinclude it.  */
/* glibc's intent is to support the IEC 559 math functionality, real
   and complex.  If the GCC (4.9 and later) predefined macros
   specifying compiler intent are available, use them to determine
   whether the overall intent is to support these features; otherwise,
   presume an older compiler has intent to support these features and
   define these macros by default.  */
/* wchar_t uses Unicode 10.0.0.  Version 10.0 of the Unicode Standard is
   synchronized with ISO/IEC 10646:2017, fifth edition, plus
   the following additions from Amendment 1 to the fifth edition:
   - 56 emoji characters
   - 285 hentaigana
   - 3 additional Zanabazar Square characters */
//1
/* 
 * bitXor - x^y using only ~ and & 
 *   Example: bitXor(4, 5) = 1
 *   Legal ops: ~ &
 *   Max ops: 14
 *   Rating: 1
 */
int bitXor(int x, int y)
{
  // Using De Morgan's laws
  return ~(~x&~y)&~(x&y);
}
/* 
 * tmin - return minimum two's complement integer 
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 4
 *   Rating: 1
 */
int tmin(void)
{
  // 0x1 left shifting 31 digits gets 0x80000000, which is the minimum
  return 1 << 31;
}
//2
/*
 * isTmax - returns 1 if x is the maximum, two's complement number,
 *     and 0 otherwise 
 *   Legal ops: ! ~ & ^ | +
 *   Max ops: 10
 *   Rating: 1
 */
int isTmax(int x)
{
  // Identifying x+1 and excluding -1
  return !((x + x + 2) + !(x + 1));
}
/* 
 * allOddBits - return 1 if all odd-numbered bits in word set to 1
 *   where bits are numbered from 0 (least significant) to 31 (most significant)
 *   Examples allOddBits(0xFFFFFFFD) = 0, allOddBits(0xAAAAAAAA) = 1
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 12
 *   Rating: 2
 */
int allOddBits(int x)
{
  // Creating a mask of the odd bits
  int mask = 0xAA + (0xAA << 8) + ((0xAA + (0xAA << 8)) << 16);
  return !((x & mask) ^ mask);
}
/* 
 * negate - return -x 
 *   Example: negate(1) = -1.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 5
 *   Rating: 2
 */
int negate(int x)
{
  // Finding the inverse for addition
  return (~x) + 1;
}
//3
/* 
 * isAsciiDigit - return 1 if 0x30 <= x <= 0x39 (ASCII codes for characters '0' to '9')
 *   Example: isAsciiDigit(0x35) = 1.
 *            isAsciiDigit(0x3a) = 0.
 *            isAsciiDigit(0x05) = 0.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 15
 *   Rating: 3
 */
int isAsciiDigit(int x)
{
  // Subtract 0x30 from x and check if the result is between 0 and 9
  int y = x + (~0x30 + 1); // x - 0x30
  int z = y + (~0xA + 1);  // y - 10
  // y should be non-negative and z should be negative
  int sign_y = (y >> 31) & 1;
  int sign_z = (z >> 31) & 1;
  return (!sign_y) & sign_z;
}
/* 
 * conditional - same as x ? y : z 
 *   Example: conditional(2,4,5) = 4
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 16
 *   Rating: 3
 */
int conditional(int x, int y, int z)
{
  // Use !! to convert x to 0 or 1
  int mask = !!x;
  // Create a mask of either all 0s or all 1s
  mask = ~mask + 1;
  // Use & and | to select either y or z based on the mask
  return (mask & y) | (~mask & z);
}

/* 
 * isLessOrEqual - if x <= y  then return 1, else return 0 
 *   Example: isLessOrEqual(4,5) = 1.
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 24
 *   Rating: 3
 */
int isLessOrEqual(int x, int y)
{
  // Extract the sign of x and y
  int sign_x = (x >> 31) & 1;
  int sign_y = (y >> 31) & 1;

  // Check if x and y have different signs
  int diff_sign = sign_x ^ sign_y;

  // Check if x is negative
  int x_is_neg = sign_x;

  // Subtract x from y and check the sign of the result
  int sub = y + (~x + 1);
  int sub_is_neg = (sub >> 31) & 1;

  // Combine the two cases
  int result = (diff_sign & x_is_neg) | (!diff_sign & !sub_is_neg);

  // Return the logical negation of the result
  return result;
}
//4
/* 
 * logicalNeg - implement the ! operator, using all of 
 *              the legal operators except !
 *   Examples: logicalNeg(3) = 0, logicalNeg(0) = 1
 *   Legal ops: ~ & ^ | + << >>
 *   Max ops: 12
 *   Rating: 4 
 */
int logicalNeg(int x)
{
  // negate x by flipping all bits and adding 1
  int neg_x = ~x + 1;
  // bitwise or x and neg_x to get the sign bit, shift right by 31 bits to get either 0 or -1
  int sign = (x | neg_x) >> 31;
  // add 1 to convert -1 to 0 and 0 to 1
  return sign + 1;
}
/* howManyBits - return the minimum number of bits required to represent x in
 *             two's complement
 *  Examples: howManyBits(12) = 5
 *            howManyBits(298) = 10
 *            howManyBits(-5) = 4
 *            howManyBits(0)  = 1
 *            howManyBits(-1) = 1
 *            howManyBits(0x80000000) = 32
 *  Legal ops: ! ~ & ^ | + << >>
 *  Max ops: 90
 *  Rating: 4
 */
int howManyBits(int x) 
{
    int n = 0; // Initialize the counter to zero
    x ^= (x >> 31); // If x is negative, flip all the bits
    n += ((!!(x >> (n + 16))) << 4); // Add 16 to n if the upper 16 bits of x are not zero
    n += ((!!(x >> (n + 8))) << 3); // Add 8 to n if the upper 8 bits of the remaining bits of x are not zero
    n += ((!!(x >> (n + 4))) << 2); // Add 4 to n if the upper 4 bits of the remaining bits of x are not zero
    n += ((!!(x >> (n + 2))) << 1); // Add 2 to n if the upper 2 bits of the remaining bits of x are not zero
    n += ((!!(x >> (n + 1)))); // Add 1 to n if the upper bit of the remaining bits of x is not zero
    n += (x >> n); // Add 1 to n if the last bit of x is not zero
    return n + 1; // Return n plus one, since we need one more bit for the sign
}
//float
/* 
 * floatScale2 - Return bit-level equivalent of expression 2*f for
 *   floating point argument f.
 *   Both the argument and result are passed as unsigned int's, but
 *   they are to be interpreted as the bit-level representation of
 *   single-precision floating point values.
 *   When argument is NaN, return argument
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
unsigned floatScale2(unsigned uf)
{
  // First, we extract the sign, exponent, and fraction bits of uf
  unsigned sign = uf & 0x80000000; // sign = uf[31]
  unsigned exp = uf & 0x7F800000;  // exp = uf[30:23]
  unsigned frac = uf & 0x007FFFFF; // frac = uf[22:0]

  // Next, we check if uf is a special case
  if (exp == 0x7F800000)
  {            // If exp is all 1s, uf is either infinity or NaN
    return uf; // In either case, we return uf as it is
  }

  if (exp == 0)
  {                     // If exp is all 0s, uf is either zero or a denormalized number
    frac <<= 1;         // We multiply the fraction by 2 by left shifting it by 1 bit
    return sign | frac; // We return the result with the same sign as uf
  }

  // Otherwise, uf is a normalized number
  exp += 0x00800000; // We add 1 to the exponent by adding 2^23
  if (exp == 0x7F800000)
  {                    // If exp becomes all 1s after adding, uf overflows to infinity
    return sign | exp; // We return infinity with the same sign as uf
  }

  // Otherwise, uf does not overflow
  return sign | exp | frac; // We return the result with the same sign, exponent, and fraction as uf
}
/* 
 * floatFloat2Int - Return bit-level equivalent of expression (int) f
 *   for floating point argument f.
 *   Argument is passed as unsigned int, but
 *   it is to be interpreted as the bit-level representation of a
 *   single-precision floating point value.
 *   Anything out of range (including NaN and infinity) should return
 *   0x80000000u.
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Max ops: 30
 *   Rating: 4
 */
int floatFloat2Int(unsigned uf)
{
  // Declare the variables first
  unsigned sign, exp, frac;
  int e, result;

  // Extract the sign, exponent, and fraction bits of uf
  sign = uf & 0x80000000; // sign = uf[31]
  exp = uf & 0x7F800000;  // exp = uf[30:23]
  frac = uf & 0x007FFFFF; // frac = uf[22:0]

  // Check if uf is a special case
  if (exp == 0x7F800000)
  {                     // If exp is all 1s, uf is either infinity or NaN
    return 0x80000000u; // In either case, return the special value 0x80000000u
  }

  if (exp == 0)
  {           // If exp is all 0s, uf is either zero or a denormalized number
    return 0; // In either case, return zero as the integer value
  }

  // Otherwise, uf is a normalized number
  e = (exp >> 23) - 127; // Calculate the actual exponent value by subtracting the bias of 127
  if (e < 0)
  {           // If e is negative, uf is less than one in magnitude
    return 0; // Return zero as the integer value
  }

  if (e > 30)
  {                     // If e is greater than 30, uf is too large to fit in a 32-bit integer
    return 0x80000000u; // Return the special value 0x80000000u
  }

  // Otherwise, uf can be converted to a valid integer
  frac |= (1 << 23); // Add the implicit leading one bit to the fraction
  result = (frac<<e)>>23; // Shift the fraction right by (23 - e) bits to align it with the integer value     
  if (sign)
  { // If sign is negative, negate the result
    result = -result;
  }

  return result;
}
// #include "floatPower2.c"
