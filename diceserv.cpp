/* ----------------------------------------------------------------------------
 * Name    : diceserv.cpp
 * Author  : Naram Qashat (CyberBotX)
 * Version : 3.0.1
 * Date    : (Last modified) February 4, 2016
 * ----------------------------------------------------------------------------
 * The following applies to the non-Anope-derived portions of the code
 * (excluding the RNG):

The MIT License (MIT)

Copyright (c) 2004-2016 Naram Qashat

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

 * (This basically covers the core functionality of DiceServ.)
 *
 * The following applies to the Anope-derived portions of the code:
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation; either version 1, or (at your option) any later
 * version.
 * ----------------------------------------------------------------------------
 * Requires: Anope 2.0.x
 * ----------------------------------------------------------------------------
 * Description:
 *
 * A dice rolling pseudo-client, mainly useful for playing pen & paper RPGs,
 * such as Dungeons and Dragons, over IRC.
 * ----------------------------------------------------------------------------
 * Configuration example can be found in diceserv.example.conf.
 * ----------------------------------------------------------------------------
 * Changelog:
 *
 * 3.0.1 - Fixed issues with loading an old DiceServ database so it actually
 *           works (there was a typo in the configuration file plus a timer
 *           has to be used).
 *       - Made a specialization of stringify for double to correct issues
 *           with some numbers using scientific notation when they shouldn't
 *           have as well as bring the precision back up.
 *       - Fixed EARTHDAWN on *nix-based systems.
 *       - Fixed DND3ECHAR so it actually works.
 * 3.0.0 - Massive rewrite, now only targets Anope 2.0.x and has been heavily
 *           modularized.
 *       - Added support for functions to have an arbitrary number of
 *           arguments, used by only the max and min function currently.
 *       - Better handling of when to switch from long-form extended output to
 *           short-form extended output to no extended output.
 *       - Made sure that the math functions that were added for use with
 *           Visual Studio are only compiled in for Visual Studio 2012 or
 *           earlier, as they were finally included with Visual Studio 2013.
 *       - Completely restructued how results are handled.
 *       - Removed dtoa function as Anope's stringify could be used to replace
 *           it (at the cost of lower output precision on floating-point
 *           values).
 *       - Replaced the Mersenne Twister RNG with a combination RNG of a
 *           SIMD-oriented Fast Mersenne Twister RNG and a Mother-of-all RNG.
 *       - Added atan2 math function.
 * 2.0.3 - Fix some memory leaks that went unnoticed by me until recently.
 * 2.0.2 - Fix a crash bug for the Anope 1.8.x versions and a lack of an error
 *           message for the Anope 1.9.x versions caused if there is nothing
 *           before or after the tilde.
 * 2.0.1 - Minor fix of permission in DiceServ's SET command.
 *       - Minor edit of GECOS of DiceServ to use "Service" instead of
 *           "Server".
 *       - Added version for Anope 1.9.5.
 *   2.0 - Replaced Coda's expression parser with a parser of my own that
 *           converts the expression from infix to postfix using the
 *           shunting-yard algorithm and then evaluates it.
 *       - Added support for DnD3e character creation rolls.
 *       - Removed Exalted dice rolls from the service, I'm not 100% sure they
 *           were ever being done right.
 *       - Used enums for the dice roll types and errors for easier usage.
 *       - Fixed overflow checks.
 *       - Allow for d% anywhere in an expression, suggested by Namegduf.
 *       - Split apart parsing the expression and evaluating it, suggested by
 *           Namegduf.
 *       - Better buffer overflow checking, and removed check for the
 *           expression being too long, the current parser can handle long
 *           expressions unlike the last parser (no offense to Coda).
 *       - Added support for the pen & paper RPG Earthdawn, suggested by
 *           DukePyrolator.
 *       - Added support for math functions. (such as sqrt, trunc, cos, etc.)
 *       - Added support for the math constants of e and pi.
 *       - Added a CALC command which is like ROLL but without rounding.
 *       - Added configuration options for DiceServ's pseudo-client name as
 *           well as giving a network-wide ability for channel operators to
 *           set DiceServ channel ignores.
 *       - Added functionality for a shorter extended output if showing the
 *           results of each individual roll would be too long to display.
 *       - Better way of determining when to display the extended output
 *           buffer.
 *       - Utilize the Mersenne Twister RNG (random number generator) instead
 *           of Anope's RNG, it's faster but uses up a bit more memory. As a
 *           result, Coda's algorithm used in the dice roller is not longer
 *           used.
 *       - Added support for dual-argument functions of max(), min, and rand().
 *   1.0 - Initial version (was only part of an Epona 1.4.14 edit).
 *       - Contained expression parser and dice roller algorithms from Adam
 *           Higerd (Coda Highland).
 *
 * ----------------------------------------------------------------------------
 */

/* RequiredLibraries: m */

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdlib>
#include <ctime>
#include "diceserv.h"
#ifdef _MSC_VER
# include <float.h>
#endif
#include <emmintrin.h>

static const int DICE_MAX_TIMES = 25;
static const unsigned DICE_MAX_DICE = 99999;
static const unsigned DICE_MAX_SIDES = 99999;

/** Determine if the double-precision floating point value is infinite or not.
 * @param num The double-precision floating point value to check
 * @return true if the value is infinite, false otherwise
 */
static inline bool is_infinite(double num)
{
#ifdef _MSC_VER
	int fpc = _fpclass(num);
	return fpc == _FPCLASS_NINF || fpc == _FPCLASS_PINF;
#else
	return std::isinf(num);
#endif
}

/** Determine if the double-precision floating point value is NaN (Not a Number) or not.
 * @param num The double-precision floating point value to check
 * @return true if the value is NaN, false otherwise
 */
static inline bool is_notanumber(double num)
{
#ifdef _MSC_VER
	int fpc = _fpclass(num);
	return fpc == _FPCLASS_SNAN || fpc == _FPCLASS_QNAN;
#else
	return std::isnan(num);
#endif
}

#if defined(_MSC_VER) && _MSC_VER < 1800
/** Calculate inverse hyperbolic cosine for Windows (only needed when compiling with Visual Studio 2012 or earlier).
 * @param num The double-precision floating point value to calculate
 * @return The inverse hyperbolic cosine of the value
 */
static inline double acosh(double num)
{
	return std::log(num + std::sqrt(num - 1) * std::sqrt(num + 1));
}

/** Calculate inverse hyperbolic sine for Windows (only needed when compiling with Visual Studio 2012 or earlier).
 * @param num The double-precision floating point value to calculate
 * @return The inverse hyperbolic sine of the value
 */
static inline double asinh(double num)
{
	return std::log(num + std::sqrt(num * num + 1));
}

/** Calculate inverse hyperbolic tangent for Windows (only needed when compiling with Visual Studio 2012 or earlier).
 * @param num The double-precision floating point value to calculate
 * @return The inverse hyperbolic tangent of the value
 */
static inline double atanh(double num)
{
	return 0.5 * std::log((1 + num) / (1 - num));
}

/** Calculate cube root for Windows (only needed when compiling with Visual Studio 2012 or earlier).
 * @param num The double-percision floating point value to calculate
 * @return The cube root of the value
 */
static inline double cbrt(double num)
{
	return std::pow(num, 1.0 / 3.0);
}
#endif

/** A combination RNG, consisting of a SIMD-oriented Fast Mersenne Twister (SFMT) RNG and Mother-of-all RNG.
 *
 * SMFT is an improvement of the Mersenne Twister with better randomness and higher speed.
 * Mother-of-all is an older multiply-with-carry generator.
 * This is a combination of the two, with improved randomness.
 *
 * This class was copied from Agner Fog's C++ class library of uniform
 * random number generators, obtained from http://www.agner.org/random/
 * Modified by Naram Qashat to only include what was needed by DiceServ,
 * as well as containing everything within the class. Also modified so the
 * Mother-of-all generator was actually seeded properly through RandomInit().
 *
 * The following license applies to this class:
 *
 * GNU General Public License http://www.gnu.org/licenses/gpl.html
 * This C++ implementation of SFMT contains parts of the original C code
 * which was published under the following BSD license, which is therefore
 * in effect in addition to the GNU General Public License.

Copyright (c) 2006, 2007 by Mutsuo Saito, Makoto Matsumoto and Hiroshima University.
Copyright (c) 2008 by Agner Fog.
All rights reserved.
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    > Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.
    > Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.
    > Neither the name of the Hiroshima University nor the names of its
      contributors may be used to endorse or promote products derived from
      this software without specific prior written permission.
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
class SFMT_Mother
{
	static const int SFMT_N = 88; // Size of state vector
	static const int SFMT_M = 68; // Position of intermediate feedback
	static const int SFMT_SL1 = 14; // Left shift of W[N-1], 32-bit words
	static const int SFMT_SL2 = 3; // Left shift of W[0], *8, 128-bit words
	static const int SFMT_SR1 = 7; // Right shift of W[M], 32-bit words
	static const int SFMT_SR2 = 3; // Right shift of W[N-2], *8, 128-bit words
	static const uint32_t SFMT_MASK[]; // AND mask
	static const uint32_t SFMT_PARITY[]; // Period certification vector

	uint32_t ix; // Index into state array
	uint32_t LastInterval; // Last interval length for IRandomX
	uint32_t RLimit; // Rejection limit used by IRandomX
	__m128i mask; // AND mask
	//__m128i state[SFMT_N]; // State vector for SFMT generator
	union
	{
		__m128i state128[SFMT_N];
		uint32_t state32[4 * SFMT_N];
	};
	uint32_t MotherState[5]; // State vector for Mother-Of-All generator

	// Subfunction for the sfmt algorithm
	static __m128i sfmt_recursion(const __m128i &a, const __m128i &b, const __m128i &c, const __m128i &d, const __m128i &mask)
	{
		__m128i b1 = _mm_srli_epi32(b, SFMT_SR1);
		__m128i a1 = _mm_slli_si128(a, SFMT_SL2);
		__m128i c1 = _mm_srli_si128(c, SFMT_SR2);
		__m128i d1 = _mm_slli_epi32(d, SFMT_SL1);
		b1 = _mm_and_si128(b1, mask);
		__m128i z1 = _mm_xor_si128(a, a1);
		__m128i z2 = _mm_xor_si128(b1, d1);
		z1 = _mm_xor_si128(z1, c1);
		z2 = _mm_xor_si128(z1, z2);
		return z2;
	}

	void Init2()
	{
		// Initialize mask
		this->mask = _mm_loadu_si128(reinterpret_cast<const __m128i *>(SFMT_MASK));

		// Period certification
		// Check if SFMT_PARITY & state[0] has odd parity
		uint32_t i, temp = 0;
		for (i = 0; i < 4; ++i)
			temp ^= SFMT_PARITY[i] & this->state32[i];
		for (i = 16; i > 0; i >>= 1)
			temp ^= temp >> i;
		if (!(temp & 1))
			// parity is even. Certification failed
			// Find a nonzero bit in period certification vector
			for (i = 0; i < 4; ++i)
				if (SFMT_PARITY[i])
					for (uint32_t j = 1; j; j <<= 1)
						if (SFMT_PARITY[i] & j)
						{
							// Flip the corresponding bit in state[0] to change parity
							this->state32[i] ^= j;
							// Done. Exit i and j loops
							i = 5;
							break;
						}
		// Generate first random numbers and set ix = 0
		this->Generate();
	}

	void Generate()
	{
		// Fill state array with new random numbers
		__m128i r, r1 = this->state128[SFMT_N - 2], r2 = this->state128[SFMT_N - 1];
		int i;
		for (i = 0; i < SFMT_N - SFMT_M; ++i)
		{
			r = sfmt_recursion(this->state128[i], this->state128[i + SFMT_M], r1, r2, this->mask);
			this->state128[i] = r;
			r1 = r2;
			r2 = r;
		}
		for (; i < SFMT_N; ++i)
		{
			r = sfmt_recursion(this->state128[i], this->state128[i + SFMT_M - SFMT_N], r1, r2, this->mask);
			this->state128[i] = r;
			r1 = r2;
			r2 = r;
		}
		this->ix = 0;
	}

	uint32_t MotherBits()
	{
		// Get random bits from Mother-Of-All generator
		uint64_t sum = static_cast<uint64_t>(2111111111U) * static_cast<uint64_t>(this->MotherState[3]) +
			static_cast<uint64_t>(1492) * static_cast<uint64_t>(this->MotherState[2]) +
			static_cast<uint64_t>(1776) * static_cast<uint64_t>(this->MotherState[1]) +
			static_cast<uint64_t>(5115) * static_cast<uint64_t>(this->MotherState[0]) +
			static_cast<uint64_t>(this->MotherState[4]);
		this->MotherState[3] = this->MotherState[2];
		this->MotherState[2] = this->MotherState[1];
		this->MotherState[1] = this->MotherState[0];
		this->MotherState[4] = static_cast<uint32_t>(sum >> 32); // Carry
		this->MotherState[0] = static_cast<uint32_t>(sum); // Low 32 bits of sum
		return this->MotherState[0];
	}

public:
	SFMT_Mother(int seed) : LastInterval(0)
	{
		this->RandomInit(seed);
	}

	/** Re-initializes the random number generator with a new seed.
	 * @param seed The value used to seed the generator.
	 */
	void RandomInit(int seed)
	{
		// Re-seed
		uint32_t y = seed; // Temporary
		static const uint32_t statesize = SFMT_N * 4 + 5; // Size of state vector

		// Fill state vector with random numbers from seed
		this->state32[0] = y;
		static const uint32_t factor = 1812433253U; // Multiplication factor

		uint32_t i;
		for (i = 1; i < statesize; ++i)
		{
			y = factor * (y ^ (y >> 30)) + i;
			if (i < statesize - 5)
				this->state32[i] = y;
			else
				this->MotherState[i + 5 - statesize] = y;
		}

		// Further initialization and period certification
		this->Init2();
	}

	/** Generate a random integer within the given range.
	 * @param min The minimum value of the range
	 * @param max The maximum value of the range
	 * @return An integer in the interval min <= x <= max
	 */
	int IRandomX(int min, int max)
	{
		// Output random integer in the interval min <= x <= max
		// Each output value has exactly the same probability.
		// This is obtained by rejecting certain bit values so that the number
		// of possible bit values is divisible by the interval length
		if (max <= min)
		{
			if (max == min)
				return min; // max == min. Only one possible value
			else
				return 0x80000000; // max < min. Error output
		}
		// Assume 64 bit integers supported. Use multiply and shift method
		uint32_t interval = static_cast<uint32_t>(max - min + 1); // Length of interval
		if (interval != this->LastInterval)
		{
			// Interval length has changed. Must calculate rejection limit
			// Reject when remainder = 2^32 / interval * interval
			// RLimit will be 0 if interval is a power of 2. No rejection then.
			this->RLimit = static_cast<uint32_t>((static_cast<uint64_t>(1) << 32) / interval) * interval - 1;
			this->LastInterval = interval;
		}
		uint32_t remainder; // Longran % 2^32
		uint32_t iran; // Longran / 2^32
		do // Rejection loop
		{
			uint64_t longran = static_cast<uint64_t>(this->BRandom()) * interval; // Random bits * interval
			iran = static_cast<uint32_t>(longran >> 32);
			remainder = static_cast<uint32_t>(longran);
		} while (remainder > this->RLimit);
		// Convert back to signed and return result
		return static_cast<int32_t>(iran) + min;
	}

	/** Generate 32 random bits.
	 * @return The random bits generated.
	 */
	uint32_t BRandom()
	{
		// Output 32 random bits
		if (this->ix >= SFMT_N * 4)
			this->Generate();
		uint32_t y = this->state32[this->ix++];
		y += this->MotherBits();
		return y;
	}
};

const uint32_t SFMT_Mother::SFMT_MASK[] = { 0xeffff7fb, 0xffffffef, 0xdfdfbfff, 0x7fffdbfd };
const uint32_t SFMT_Mother::SFMT_PARITY[] = { 1, 0, 0xe8148000, 0xd0c7afa3 };

static SFMT_Mother sfmtRNG(static_cast<int>(std::time(NULL)));

/** Determine if the given character is a number.
 * @param chr Character to check
 * @return true if the character is a number, false otherwise
 */
static inline bool is_number(char chr)
{
	return (chr >= '0' && chr <= '9') || chr == '.';
}

/** Determine if the given character is a multiplication or division operator.
 * @param chr Character to check
 * @return true if the character is a multiplication or division operator, false otherwise
 */
static inline bool is_muldiv(char chr)
{
	return chr == '%' || chr == '/' || chr == '*';
}

/** Determine if the given character is an addition or subtraction operator.
 * @param chr Character to check
 * @return true if the character is an addition or subtraction operator, false otherwise
 */
static inline bool is_plusmin(char chr)
{
	return chr == '+' || chr == '-';
}

/** Determine if the given character is an operator of any sort, except for parenthesis.
 * @param chr Character to check
 * @return true if the character is a non-parenthesis operator, false otherwise
 */
static inline bool is_op_noparen(char chr)
{
	return is_plusmin(chr) || is_muldiv(chr) || chr == '^' || chr == 'd';
}

/** Determine if the given character is an operator of any sort.
 * @param chr Character to check
 * @return true if the character is an operator, false otherwise
 */
static inline bool is_operator(char chr)
{
	return chr == '(' || chr == ')' || is_op_noparen(chr);
}

/** Determine if the substring portion of the given string is a function.
 * @param str String to check
 * @param pos Starting position of the substring to check, defaults to 0
 * @return 0 if the string isn't a function, or a number corresponding to the length of the function name
 */
static inline unsigned is_function(const Anope::string &str, unsigned pos = 0)
{
	// We only need a 5 character substring as that's the largest substring we will be looking at
	Anope::string func = str.substr(pos, 5);
	// acosh, asinh, atan2 atanh, floor, log10, round, trunc
	Anope::string func_5 = func.substr(0, 5);
	if (func_5.equals_ci("acosh") || func_5.equals_ci("asinh") || func_5.equals_ci("atan2") || func_5.equals_ci("atanh") || func_5.equals_ci("floor") ||
		func_5.equals_ci("log10") || func_5.equals_ci("round") || func_5.equals_ci("trunc"))
		return 5;
	// acos, asin, atan, cbrt, ceil, cosh, rand, sinh, sqrt, tanh
	Anope::string func_4 = func.substr(0, 4);
	if (func_4.equals_ci("acos") || func_4.equals_ci("asin") || func_4.equals_ci("atan") || func_4.equals_ci("cbrt") || func_4.equals_ci("ceil") ||
		func_4.equals_ci("cosh") || func_4.equals_ci("rand") || func_4.equals_ci("sinh") || func_4.equals_ci("sqrt") || func_4.equals_ci("tanh"))
		return 4;
	// abs, cos, deg, exp, fac, log, max, min, rad, sin, tan
	Anope::string func_3 = func.substr(0, 3);
	if (func_3.equals_ci("abs") || func_3.equals_ci("cos") || func_3.equals_ci("deg") || func_3.equals_ci("exp") || func_3.equals_ci("fac") ||
		func_3.equals_ci("log") || func_3.equals_ci("max") || func_3.equals_ci("min") || func_3.equals_ci("rad") || func_3.equals_ci("sin") ||
		func_3.equals_ci("tan"))
		return 3;
	// None of the above
	return 0;
}

/** Determine the number of arguments that the given function needs.
 * @param str Function string to check
 * @return Returns 1 except for the min and max functions which return -2 (to say they require AT LEAST 2 arguments), and the atan2 and rand functions which return 2
 */
static inline int function_argument_count(const Anope::string &str)
{
	Anope::string func_3 = str.substr(0, 3);
	if (func_3.equals_ci("max") || func_3.equals_ci("min"))
		return -2;
	if (str.equals_ci("atan2") || str.equals_ci("rand"))
		return 2;
	return 1;
}

/** Determine if the substring portion of the given string is a constant (currently only e and pi).
 * @param str String to check
 * @param pos Starting position of the substring to check, defaults to 0
 * @return 0 if the string isn't a constant, or a number corresponding to the length of the constant's name
 */
static inline unsigned is_constant(const Anope::string &str, unsigned pos = 0)
{
	// We only need a 2 character substring as that's the largest substring we will be looking at
	Anope::string constant = str.substr(pos, 2);
	// pi
	if (constant.substr(0, 2).equals_ci("pi"))
		return 2;
	// e
	if (constant.substr(0, 1).equals_ci("e"))
		return 1;
	// None of the above
	return 0;
}

/** Determine if the given operator has a higher precendence than the operator on the top of the stack during infix to postfix conversion.
 * @param adding The operator we are adding to the stack, or an empty string if nothing is being added and we just want to remove
 * @param topstack The operator that was at the top of the operator stack
 * @return 0 if the given operator has the same or lower precendence (and won't cause a pop), 1 if the operator has higher precendence (and will cause a pop)
 *
 * In addition to the above in regards to the return value, there are other situations. If the top of the stack is an open parenthesis,
 * or is empty, a 0 will be returned to stop the stack from popping anything else. If nothing is being added to the stack and the previous
 * sitation hasn't occurred, a 1 will be returned to signify to continue popping the stack until the previous sitation occurs. If the operator
 * being added is a function, we return 0 to signify we aren't popping. If the top of the stack is a function, we return 1 to signify we are
 * popping. A -1 is only returned if an invalid operator is given, hopefully that will never happen.
 */
static inline int would_pop(const Anope::string &adding, const Anope::string &topstack)
{
	if (adding.empty())
		return topstack.empty() || topstack == "(" ? 0 : 1;
	if (is_function(adding))
		return 0;
	if (topstack.empty() || topstack == "(")
		return 0;
	if (is_function(topstack))
		return 1;
	if (topstack == adding && adding != "^")
		return 1;
	switch (adding[0])
	{
		case 'd':
			return 0;
		case '^':
			return topstack.equals_ci("d") ? 1 : 0;
		case '%':
		case '/':
		case '*':
			return topstack == "^" || topstack.equals_ci("d") || is_muldiv(topstack[0]) ? 1 : 0;
		case '+':
		case '-':
			return is_op_noparen(topstack[0]) ? 1 : 0;
	}
	return -1;
}

/** Calculate a die roll for the given number of sides for a set number of times.
 * @param num Number of times to throw the die
 * @param sides Number of sides on the die
 * @return The results of the dice in a special structure
 */
DiceResult Dice(int num, unsigned sides)
{
	DiceResult result = DiceResult(num, sides);
	for (int i = 0; i < num; ++i)
		// Get a random number between 1 and the number of sides
		result.AddResult(sfmtRNG.IRandomX(1, sides));
	return result;
}

/** Round a value to the given number of decimals, originally needed for Windows but also used for other OSes as well due to undefined references.
 * @param val The value to round
 * @param decimals The number of digits after the decimal point, defaults to 0
 * @return The rounded value
 *
 * NOTE: Function is a slightly modified form of the code from this page:
 * http://social.msdn.microsoft.com/forums/en-US/vclanguage/thread/a7d4bf31-6c32-4b25-bc76-21b29f5287a1/
 */
static double my_round(double val, unsigned decimals = 0)
{
	if (!val) // val must be different from zero to avoid division by zero!
		return 0;
	double sign = std::abs(val) / val; // we obtain the sign to calculate positive always
	double tempval = std::abs(val * std::pow(10.0, static_cast<double>(decimals))); // shift decimal places
	unsigned tempint = static_cast<unsigned>(tempval);
	double decimalpart = tempval - tempint; // obtain just the decimal part
	if (decimalpart >= 0.5)
		tempval = std::ceil(tempval); // next integer number if greater or equal to 0.5
	else
		tempval = std::floor(tempval); // otherwise stay in the current interger part
	return (tempval * std::pow(10.0, -static_cast<int>(decimals))) * sign; // shift again to the normal decimal places
}

/** Structure to store the infix notation string as well as the positions each character is compared to the original input */
struct Infix
{
	Anope::string str;
	std::vector<unsigned> positions;

	Infix(const Anope::string &newStr, std::vector<unsigned> newPositions)
	{
		this->str = newStr;
		this->positions = newPositions;
	}

	Infix(const Anope::string &newStr, unsigned newPositions[], unsigned num)
	{
		this->str = newStr;
		this->positions = std::vector<unsigned>(newPositions, newPositions + sizeof(unsigned) * num);
	}
};

/** Fix an infix notation equation.
 * @param infix The original infix notation equation
 * @return A fixed infix notation equation
 *
 * This will convert a single % to 1d100, place a 1 in front of any d's that have no numbers before them, change all %'s after a d into 100,
 * add *'s for implicit multiplication, and convert unary -'s to _ for easier parsing later.
 */
static Infix FixInfix(const Anope::string &infix)
{
	if (infix == "%")
	{
		unsigned tmp[] = { 0, 0, 0, 0, 0 };
		return Infix("1d100", tmp, 5);
	}
	bool prev_was_func = false, prev_was_const = false;
	Anope::string newinfix;
	std::vector<unsigned> positions;
	unsigned len = infix.length();
	for (unsigned x = 0; x < len; ++x)
	{
		// Check for a function, and skip it if it exists
		unsigned func = is_function(infix, x);
		if (func)
		{
			if (x && is_number(infix[x - 1]))
			{
				newinfix += '*';
				positions.push_back(x);
			}
			newinfix += infix.substr(x, func);
			for (unsigned y = 0; y < func; ++y)
				positions.push_back(x + y);
			x += func - 1;
			prev_was_func = true;
			continue;
		}
		// Check for a constant, and skip it if it exists
		unsigned constant = is_constant(infix, x);
		if (constant)
		{
			if (x && is_number(infix[x - 1]))
			{
				newinfix += '*';
				positions.push_back(x);
			}
			newinfix += infix.substr(x, constant);
			for (unsigned y = 0; y < constant; ++y)
				positions.push_back(x + y);
			if (x + constant < len && (is_number(infix[x + constant]) || is_constant(infix, x + constant) || is_function(infix, x + constant)))
			{
				newinfix += '*';
				positions.push_back(x + constant);
			}
			x += constant - 1;
			prev_was_const = true;
			continue;
		}
		char curr = static_cast<char>(std::tolower(infix[x]));
		if (curr == 'd')
		{
			positions.push_back(x);
			if (!x)
			{
				newinfix += "1d";
				positions.push_back(x);
			}
			else
			{
				if (!is_number(infix[x - 1]) && infix[x - 1] != ')' && !prev_was_const)
				{
					newinfix += '1';
					positions.push_back(x);
				}
				newinfix += 'd';
			}
			if (x != len - 1 && infix[x + 1] == '%')
			{
				newinfix += "100";
				++x;
				positions.push_back(x);
				positions.push_back(x);
			}
		}
		else if (curr == '(')
		{
			if (x && !prev_was_func && (is_number(infix[x - 1]) || prev_was_const))
			{
				newinfix += '*';
				positions.push_back(x);
			}
			newinfix += '(';
			positions.push_back(x);
		}
		else if (curr == ')')
		{
			newinfix += ')';
			positions.push_back(x);
			if (x != len - 1 && (is_number(infix[x + 1]) || infix[x + 1] == '(' || is_constant(infix, x + 1)))
			{
				newinfix += '*';
				positions.push_back(x);
			}
		}
		else if (curr == '-')
		{
			positions.push_back(x);
			if (x != len - 1 && (!x ? 1 : is_op_noparen(static_cast<char>(std::tolower(infix[x - 1]))) || infix[x - 1] == '(' || infix[x - 1] == ','))
			{
				if (infix[x + 1] == '(' || is_function(infix, x + 1))
				{
					newinfix += "0-";
					positions.push_back(x);
				}
				else if (is_number(infix[x + 1]) || is_constant(infix, x + 1))
					newinfix += '_';
				else
					newinfix += '-';
			}
			else
				newinfix += '-';
		}
		else
		{
			newinfix += curr;
			positions.push_back(x);
		}
		prev_was_func = prev_was_const = false;
	}
	positions.push_back(len);
	return Infix(newinfix, positions);
}

/** Validate an infix notation equation.
 * @param infix The infix notation equation to validate
 * @return false for an invalid equation, true for a valid one
 *
 * The validation is as follows:
 * - All functions must have an open parenthesis after them.
 * - A comma must be prefixed by a number or close parenthesis and must be suffixed by a number, open parenthesis, _ for unary minus, constant, or function.
 * - All non-parentheis operators must be prefixed by a number or close parenthesis and suffixed by a number, open parenthesis, _ for unary minus, constant, or function.
 * - All open parentheses must be prefixed by an operator, open parenthesis, or comma and suffixed by a number, an open parenthesis, _ for unary minus, constant, or function.
 * - All close parentheses must be prefixed by a number or close parenthesis and suffixed by an operator, close parenthesis, or comma.
 */
static bool CheckInfix(DiceServData &data, const Infix &infix)
{
	bool prev_was_func = false, prev_was_const = false;
	for (unsigned x = 0, len = infix.str.length(); x < len; ++x)
	{
		unsigned position = infix.positions[x];
		// Check for a function, and skip it if it exists
		unsigned func = is_function(infix.str, x);
		if (func)
		{
			if ((x + func < len && infix.str[x + func] != '(') || x + func >= len)
			{
				data.errPos = infix.positions[x + func >= len ? len : x + func];
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No open parenthesis found after function.";
				return false;
			}
			x += func - 1;
			prev_was_func = true;
			continue;
		}
		// Check for a constant, and skip it if it exists
		unsigned constant = is_constant(infix.str, x);
		if (constant)
		{
			x += constant - 1;
			prev_was_const = true;
			continue;
		}
		if (infix.str[x] == ',')
		{
			if (!x ? 1 : !is_number(infix.str[x - 1]) && infix.str[x - 1] != ')' && !prev_was_const)
			{
				data.errPos = position;
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No number or close parenthesis before comma.";
				return false;
			}
			if (x == len - 1 ? 1 : !is_number(infix.str[x + 1]) && infix.str[x + 1] != '(' && infix.str[x + 1] != '_' && !is_constant(infix.str, x + 1) &&
				!is_function(infix.str, x + 1))
			{
				data.errPos = position;
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No number or open parenthesis after comma.";
				return false;
			}
		}
		else if (is_op_noparen(infix.str[x]))
		{
			if (!x ? 1 : !is_number(infix.str[x - 1]) && infix.str[x - 1] != ')' && !prev_was_const)
			{
				data.errPos = position;
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No number or close parenthesis before operator.";
				return false;
			}
			if (x == len - 1 ? 1 : !is_number(infix.str[x + 1]) && infix.str[x + 1] != '(' && infix.str[x + 1] != '_' && !is_constant(infix.str, x + 1) &&
				!is_function(infix.str, x + 1))
			{
				data.errPos = position;
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No number or open parenthesis after operator.";
				return false;
			}
		}
		else if (infix.str[x] == '(')
		{
			if (x && !is_op_noparen(infix.str[x - 1]) && infix.str[x - 1] != '(' && infix.str[x - 1] != ',' && !prev_was_func)
			{
				data.errPos = position;
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No operator or open parenthesis found before current open\nparenthesis.";
				return false;
			}
			if (x != len - 1 && !is_number(infix.str[x + 1]) && infix.str[x + 1] != '(' && infix.str[x + 1] != '_' && !is_constant(infix.str, x + 1) &&
				!is_function(infix.str, x + 1))
			{
				data.errPos = position;
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No number after current open parenthesis.";
				return false;
			}
		}
		else if (infix.str[x] == ')')
		{
			if (x && !is_number(infix.str[x - 1]) && infix.str[x - 1] != ')' && !prev_was_const)
			{
				data.errPos = position;
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No number found before current close parenthesis.";
				return false;
			}
			if (x != len - 1 && !is_op_noparen(infix.str[x + 1]) && infix.str[x + 1] != ')' && infix.str[x + 1] != ',')
			{
				data.errPos = position;
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No operator or close parenthesis found after current close\nparenthesis.";
				return false;
			}
		}
		else if (!is_number(infix.str[x]) && !is_muldiv(infix.str[x]) && !is_plusmin(infix.str[x]) && !is_operator(infix.str[x]) && infix.str[x] != '_')
		{
			data.errPos = position;
			data.errCode = DICE_ERROR_PARSE;
			data.errStr = "An invalid character was encountered.";
			return false;
		}
		prev_was_func = prev_was_const = false;
	}
	return true;
}

/** Tokenize an infix notation equation by adding spaces between operators.
 * @param infix The original infix notation equation to tokenize
 * @return A new infix notation equation with spaces between operators
 */
static Infix TokenizeInfix(const Infix &infix)
{
	Anope::string newinfix;
	std::vector<unsigned> positions;
	for (unsigned x = 0, len = infix.str.length(); x < len; ++x)
	{
		unsigned position = infix.positions[x], func = is_function(infix.str, x), constant = is_constant(infix.str, x);
		char curr = infix.str[x];
		if (func)
		{
			if (x && !newinfix.empty() && newinfix[newinfix.length() - 1] != ' ')
			{
				newinfix += ' ';
				positions.push_back(position);
			}
			newinfix += infix.str.substr(x, func);
			for (unsigned y = 0; y < func; ++y)
				positions.push_back(infix.positions[x + y]);
			if (x != len - 1)
			{
				newinfix += ' ';
				positions.push_back(infix.positions[x + func]);
			}
			x += func - 1;
		}
		else if (constant)
		{
			if (x && !newinfix.empty() && newinfix[newinfix.length() - 1] != ' ' && newinfix[newinfix.length() - 1] != '_')
			{
				newinfix += ' ';
				positions.push_back(position);
			}
			newinfix += infix.str.substr(x, constant);
			for (unsigned y = 0; y < constant; ++y)
				positions.push_back(infix.positions[x + y]);
			if (x != len - 1)
			{
				newinfix += ' ';
				positions.push_back(infix.positions[x + constant]);
			}
			x += constant - 1;
		}
		else if (curr == ',')
		{
			if (x && !newinfix.empty() && newinfix[newinfix.length() - 1] != ' ')
			{
				newinfix += ' ';
				positions.push_back(position);
			}
			newinfix += ',';
			positions.push_back(position);
			if (x != len - 1)
			{
				newinfix += ' ';
				positions.push_back(position);
			}
		}
		else if (is_operator(curr))
		{
			if (x && !newinfix.empty() && newinfix[newinfix.length() - 1] != ' ')
			{
				newinfix += ' ';
				positions.push_back(position);
			}
			newinfix += curr;
			positions.push_back(position);
			if (x != len - 1)
			{
				newinfix += ' ';
				positions.push_back(position);
			}
		}
		else
		{
			newinfix += curr;
			positions.push_back(position);
		}
	}
	return Infix(newinfix, positions);
}

/** Enumeration for PostfixValue to determine it's type */
enum PostfixValueType
{
	POSTFIX_VALUE_NONE,
	POSTFIX_VALUE_DOUBLE,
	POSTFIX_VALUE_STRING
};

/** Base class for values in a postfix equation */
class PostfixValueBase
{
	PostfixValueType type;
protected:
	virtual void Clear() = 0;
public:
	PostfixValueBase() : type(POSTFIX_VALUE_NONE)
	{
	}

	PostfixValueBase(PostfixValueType t) : type(t)
	{
	}

	virtual ~PostfixValueBase()
	{
	}

	PostfixValueType Type() const
	{
		return this->type;
	}

	virtual PostfixValueBase *Clone() const = 0;
};

/** Version of PostfixValue for double */
class PostfixValueDouble : public PostfixValueBase
{
	double *val;
protected:
	void Clear()
	{
		delete this->val;
	}
public:
	PostfixValueDouble() : PostfixValueBase(POSTFIX_VALUE_DOUBLE), val(NULL)
	{
	}

	PostfixValueDouble(double Val) : PostfixValueBase(POSTFIX_VALUE_DOUBLE), val(new double(Val))
	{
	}

	PostfixValueDouble(const PostfixValueDouble &Val) : PostfixValueBase(POSTFIX_VALUE_DOUBLE), val(Val.val ? new double(*Val.val) : NULL)
	{
	}

	~PostfixValueDouble()
	{
		this->Clear();
	}

	PostfixValueDouble &operator=(const PostfixValueDouble &Val)
	{
		if (this != &Val && Val.val)
		{
			if (this->val)
				*this->val = *Val.val;
			else
				this->val = new double(*Val.val);
		}
		return *this;
	}

	const double *Get() const
	{
		return this->val;
	}

	PostfixValueDouble *Clone() const
	{
		return new PostfixValueDouble(*this);
	}
};

/** Version of PostfixValue for Anope::string */
class PostfixValueString : public PostfixValueBase
{
	Anope::string *val;
protected:
	void Clear()
	{
		delete this->val;
	}
public:
	PostfixValueString() : PostfixValueBase(POSTFIX_VALUE_STRING), val(NULL)
	{
	}

	PostfixValueString(const Anope::string &Val) : PostfixValueBase(POSTFIX_VALUE_STRING), val(new Anope::string(Val))
	{
	}
	PostfixValueString(const PostfixValueString &Val) : PostfixValueBase(POSTFIX_VALUE_STRING), val(Val.val ? new Anope::string(*Val.val) : NULL)
	{
	}

	~PostfixValueString()
	{
		this->Clear();
	}

	PostfixValueString &operator=(const PostfixValueString &Val)
	{
		if (this != &Val && Val.val)
		{
			if (this->val)
				*this->val = *Val.val;
			else
				this->val = new Anope::string(*Val.val);
		}
		return *this;
	}

	const Anope::string *Get() const
	{
		return this->val;
	}

	PostfixValueString *Clone() const
	{
		return new PostfixValueString(*this);
	}
};

/** Container for the list of Postfix values */
class Postfix
{
	std::vector<PostfixValueBase *> values;
public:
	Postfix() : values()
	{
	}

	Postfix(const Postfix &postfix) : values()
	{
		this->append(postfix);
	}

	Postfix &operator=(const Postfix &postfix)
	{
		if (this != &postfix)
		{
			this->clear();
			this->append(postfix);
		}
		return *this;
	}

	~Postfix()
	{
		this->clear();
	}

	void clear()
	{
		for (unsigned y = 0, len = this->values.size(); y < len; ++y)
			delete this->values[y];
		this->values.clear();
	}

	void add(double dbl)
	{
		this->values.push_back(new PostfixValueDouble(dbl));
	}

	void add(const Anope::string &str)
	{
		this->values.push_back(new PostfixValueString(str));
	}

	void append(const Postfix &postfix)
	{
		for (unsigned y = 0, len = postfix.values.size(); y < len; ++y)
			this->values.push_back(postfix.values[y]->Clone());
	}

	bool empty() const
	{
		return this->values.empty();
	}

	size_t size() const
	{
		return this->values.size();
	}

	PostfixValueBase *operator[](unsigned index)
	{
		if (index >= this->values.size())
			return NULL;
		return this->values[index];
	}

	const PostfixValueBase *operator[](unsigned index) const
	{
		if (index >= this->values.size())
			return NULL;
		return this->values[index];
	}
};

/** Convert an infix notation equation to a postfix notation equation, using the shunting-yard algorithm.
 * @param infix The infix notation equation to convert
 * @return A postfix notation equation
 *
 * Numbers are always stored in the postfix notation equation immediately, and operators are kept on a stack until they are
 * needed to be added to the postfix notation equation.
 * The conversion process goes as follows:
 * - Iterate through the infix notation equation, doing the following on each operation:
 *   - When a _ is encountered, add the number following it to the postfix notation equation, but make sure it's negative.
 *   - When a number is encountered, add it to the postfix notation equation.
 *   - When a function is encountered, add it to the operator stack and store a 1 on the arity stack.
 *   - When a constant is encountered, convert it to a number and add it to the postfix notation equation.
 *   - When an operator is encountered:
 *     - Check if we had any numbers prior to the operator, and fail if there were none.
 *     - Always add open parentheses to the operator stack.
 *     - When a close parenthesis is encountered, pop all operators until we get to an open parenthesis or the stack becomes
 *       empty, failing on the latter.
 *     - For all other operators, pop the stack if needed then add the operator to the stack.
 *   - When a comma is encountered, do the same as above for when a close parenthesis is encountered, but also check to make
 *     sure there was a function prior to the open parenthesis (if there is one). Increase the top of the arity stack by one.
 *   - If anything else is encountered, fail as it is an invalid value.
 * - If there were operators left on the operator stack, pop all of them, failing if anything is left on the stack (an open
 *   parenthesis will cause this).
 *
 * Of special note, when a function is being popped from the operator stack, if the function is allowed to take a variable
 * number of arguments, the number of arguments from the arity stack will be appended to the function's name, with an underscore
 * before that. The arity stack will be popped regardless.
 *
 * The improvement to the shunting-yard algorithm to allow functions to have arbitrary numbers of arguments comes from:
 * https://blog.kallisti.net.nz/2008/02/extension-to-the-shunting-yard-algorithm-to-allow-variable-numbers-of-arguments-to-functions/
 */
static Postfix InfixToPostfix(DiceServData &data, const Infix &infix)
{
	Postfix postfix;
	unsigned len = infix.str.length(), x = 0;
	bool prev_was_close = false, prev_was_number = false;
	std::stack<Anope::string> op_stack;
	std::stack<unsigned> arity_stack;
	spacesepstream tokens(infix.str);
	Anope::string token, lastone;
	while (tokens.GetToken(token))
	{
		if (token[0] == '_')
		{
			double number = 0.0;
			if (is_constant(token, 1))
			{
				if (token.substr(1).equals_ci("e"))
					number = -exp(1.0);
				else if (token.substr(1).equals_ci("pi"))
					number = -atan(1.0) * 4;
			}
			else
				number = -atof(token.substr(1).c_str());
			if (is_infinite(number) || is_notanumber(number))
			{
				data.errCode = is_infinite(number) ? DICE_ERROR_OVERUNDERFLOW : DICE_ERROR_UNDEFINED;
				postfix.clear();
				return postfix;
			}
			postfix.add(number);
			prev_was_number = true;
		}
		else if (is_number(token[0]))
		{
			double number = atof(token.c_str());
			if (is_infinite(number) || is_notanumber(number))
			{
				data.errCode = is_infinite(number) ? DICE_ERROR_OVERUNDERFLOW : DICE_ERROR_UNDEFINED;
				postfix.clear();
				return postfix;
			}
			postfix.add(number);
			prev_was_number = true;
		}
		else if (is_function(token))
		{
			op_stack.push(token);
			arity_stack.push(1);
		}
		else if (is_constant(token))
		{
			double number = 0.0;
			if (token.equals_ci("e"))
				number = exp(1.0);
			else if (token.equals_ci("pi"))
				number = atan(1.0) * 4;
			postfix.add(number);
			prev_was_number = true;
		}
		else if (is_operator(token[0]))
		{
			lastone = op_stack.empty() ? "" : op_stack.top();
			if (!prev_was_number && token != "(" && token != ")" && !prev_was_close)
			{
				data.errPos = infix.positions[x];
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "No numbers were found before the operator was encountered.";
				postfix.clear();
				return postfix;
			}
			prev_was_number = false;
			if (token == "(")
			{
				op_stack.push(token);
				prev_was_close = false;
			}
			else if (token == ")")
			{
				while (would_pop(token, lastone))
				{
					postfix.add(lastone);
					op_stack.pop();
					lastone = op_stack.empty() ? "" : op_stack.top();
				}
				if (lastone != "(")
				{
					data.errPos = infix.positions[x];
					data.errCode = DICE_ERROR_PARSE;
					data.errStr = "A close parenthesis was found but not enough open\nparentheses were found before it.";
					postfix.clear();
					return postfix;
				}
				else
					op_stack.pop();
				prev_was_close = true;
			}
			else
			{
				if (!would_pop(token, lastone))
					op_stack.push(token);
				else
				{
					while (would_pop(token, lastone))
					{
						if (is_function(lastone))
						{
							if (function_argument_count(lastone) < 0)
							{
								unsigned arity = arity_stack.top();
								Anope::string arityStr = stringify(arity);
								lastone += "_" + arityStr;
							}
							arity_stack.pop();
						}
						postfix.add(lastone);
						op_stack.pop();
						lastone = op_stack.empty() ? "" : op_stack.top();
					}
					op_stack.push(token);
				}
				prev_was_close = false;
			}
		}
		else if (token[0] == ',')
		{
			lastone = op_stack.empty() ? "" : op_stack.top();
			while (would_pop(token, lastone))
			{
				postfix.add(lastone);
				op_stack.pop();
				lastone = op_stack.empty() ? "" : op_stack.top();
			}
			if (lastone != "(")
			{
				data.errPos = infix.positions[x];
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "A comma was encountered outside of a function.";
				postfix.clear();
				return postfix;
			}
			else
			{
				Anope::string paren = lastone;
				op_stack.pop();
				lastone = op_stack.empty() ? "" : op_stack.top();
				if (!is_function(lastone))
				{
					data.errPos = infix.positions[x];
					data.errCode = DICE_ERROR_PARSE;
					data.errStr = "A comma was encountered outside of a function.";
					postfix.clear();
					return postfix;
				}
				else
				{
					op_stack.push(paren);
					++arity_stack.top();
				}
			}
		}
		else
		{
			data.errPos = infix.positions[x];
			data.errCode = DICE_ERROR_PARSE;
			data.errStr = "An invalid character was encountered.";
			postfix.clear();
			return postfix;
		}
		x += token.length() + (x ? 1 : 0);
	}
	if (!op_stack.empty())
	{
		lastone = op_stack.top();
		while (would_pop("", lastone))
		{
			if (is_function(lastone))
			{
				if (function_argument_count(lastone) < 0)
				{
					unsigned arity = arity_stack.top();
					Anope::string arityStr = stringify(arity);
					lastone += "_" + arityStr;
				}
				arity_stack.pop();
			}
			postfix.add(lastone);
			op_stack.pop();
			if (op_stack.empty())
				break;
			else
				lastone = op_stack.top();
		}
		if (!op_stack.empty())
		{
			data.errPos = len < infix.positions.size() ? infix.positions[len] : infix.positions[infix.positions.size() - 1] + 1;
			data.errCode = DICE_ERROR_PARSE;
			data.errStr = "There are more open parentheses than close parentheses.";
			postfix.clear();
			return postfix;
		}
	}
	return postfix;
}

/** Evaluate a postfix notation equation.
 * @param The postfix notation equation to evaluate
 * @return The final result after calcuation of the equation
 *
 * The evaluation pops the required values from the operand stack for a function, and 2 values from the operand stack for an operator. The result
 * of either one is placed back on the operand stack, hopefully leaving a single result at the end.
 */
static double EvaluatePostfix(DiceServData &data, const Postfix &postfix)
{
	double val = 0;
	std::stack<double> num_stack;
	for (unsigned x = 0, len = postfix.size(); x < len; ++x)
	{
		if (postfix[x]->Type() == POSTFIX_VALUE_STRING)
		{
			const PostfixValueString *str = dynamic_cast<const PostfixValueString *>(postfix[x]);
			const Anope::string *token_ptr = str->Get();
			Anope::string token = token_ptr ? *token_ptr : "";
			if (token.empty())
			{
				data.errCode = DICE_ERROR_STACK;
				data.errStr = "An empty token was found.";
				return 0;
			}
			if (is_function(token))
			{
				int function_arguments = function_argument_count(token);
				if (function_arguments < 0)
				{
					size_t underscore = token.find('_');
					int real_function_arguments = convertTo<int>(token.substr(underscore + 1));
					token = token.substr(0, underscore);
					if (real_function_arguments < -function_arguments)
					{
						data.errCode = DICE_ERROR_STACK;
						data.errStr = "Function requires at least " + stringify(-function_arguments) + " arguments, but only " +
							stringify(real_function_arguments) + " were passed.";
						return 0;
					}
					function_arguments = real_function_arguments;
				}
				if (num_stack.empty() || num_stack.size() < static_cast<unsigned>(function_arguments))
				{
					data.errCode = DICE_ERROR_STACK;
					data.errStr = "Not enough numbers for function.";
					return 0;
				}
				double val1 = num_stack.top();
				num_stack.pop();
				FunctionResult result;
				if (token.equals_ci("abs"))
				{
					val = std::abs(val1);
					result.SetNameAndResult("abs", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("acos"))
				{
					if (std::abs(val1) > 1)
					{
						data.errCode = DICE_ERROR_UNDEFINED;
						return 0;
					}
					val = std::acos(val1);
					result.SetNameAndResult("acos", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("acosh"))
				{
					if (val1 < 1)
					{
						data.errCode = DICE_ERROR_UNDEFINED;
						return 0;
					}
					val = acosh(val1);
					result.SetNameAndResult("acosh", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("asin"))
				{
					if (std::abs(val1) > 1)
					{
						data.errCode = DICE_ERROR_UNDEFINED;
						return 0;
					}
					val = std::asin(val1);
					result.SetNameAndResult("asin", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("asinh"))
				{
					val = asinh(val1);
					result.SetNameAndResult("asinh", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("atan"))
				{
					val = std::atan(val1);
					result.SetNameAndResult("atan", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("atan2"))
				{
					double val2 = val1;
					val1 = num_stack.top();
					num_stack.pop();
					val = std::atan2(val1, val2);
					result.SetNameAndResult("atan2", val);
					result.AddArgument(val1);
					result.AddArgument(val2);
				}
				else if (token.equals_ci("atanh"))
				{
					if (std::abs(val1) >= 1)
					{
						data.errCode = std::abs(val1) == 1 ? DICE_ERROR_DIV0 : DICE_ERROR_UNDEFINED;
						return 0;
					}
					val = atanh(val1);
					result.SetNameAndResult("atanh", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("cbrt"))
				{
					val = cbrt(val1);
					result.SetNameAndResult("cbrt", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("ceil"))
				{
					val = std::ceil(val1);
					result.SetNameAndResult("ceil", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("cos"))
				{
					val = std::cos(val1);
					result.SetNameAndResult("cos", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("cosh"))
				{
					val = std::cosh(val1);
					result.SetNameAndResult("cosh", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("deg"))
				{
					val = val1 * 45.0 / std::atan(1.0);
					result.SetNameAndResult("deg", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("exp"))
				{
					val = std::exp(val1);
					result.SetNameAndResult("exp", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("fac"))
				{
					if (static_cast<int>(val1) < 0)
					{
						data.errCode = DICE_ERROR_UNDEFINED;
						return 0;
					}
					val = 1;
					for (unsigned n = 2; n <= static_cast<unsigned>(val1); ++n)
						val *= n;
					result.SetNameAndResult("fac", val);
					result.AddArgument(static_cast<unsigned>(val1));
				}
				else if (token.equals_ci("floor"))
				{
					val = std::floor(val1);
					result.SetNameAndResult("floor", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("log"))
				{
					if (val1 <= 0)
					{
						data.errCode = DICE_ERROR_DIV0;
						return 0;
					}
					val = std::log(val1);
					result.SetNameAndResult("log", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("log10"))
				{
					if (val1 <= 0)
					{
						data.errCode = DICE_ERROR_DIV0;
						return 0;
					}
					val = std::log10(val1);
					result.SetNameAndResult("log10", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("max"))
				{
					std::stack<double> args;
					args.push(val1);
					for (int i = 1; i < function_arguments; ++i)
					{
						double val2 = val1;
						val1 = num_stack.top();
						num_stack.pop();
						args.push(val1);
						val = val1 = std::max(val1, val2);
					}
					result.SetNameAndResult("max", val);
					while (!args.empty())
					{
						result.AddArgument(args.top());
						args.pop();
					}
				}
				else if (token.equals_ci("min"))
				{
					std::stack<double> args;
					args.push(val1);
					for (int i = 1; i < function_arguments; ++i)
					{
						double val2 = val1;
						val1 = num_stack.top();
						num_stack.pop();
						args.push(val1);
						val = val1 = std::min(val1, val2);
					}
					result.SetNameAndResult("min", val);
					while (!args.empty())
					{
						result.AddArgument(args.top());
						args.pop();
					}
				}
				else if (token.equals_ci("rad"))
				{
					val = val1 * std::atan(1.0) / 45.0;
					result.SetNameAndResult("rad", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("rand"))
				{
					double val2 = val1;
					val1 = num_stack.top();
					num_stack.pop();
					if (val1 > val2)
					{
						double tmp = val2;
						val2 = val1;
						val1 = tmp;
					}
					val = sfmtRNG.IRandomX(static_cast<int>(val1), static_cast<int>(val2));
					result.SetNameAndResult("rand", val);
					result.AddArgument(static_cast<int>(val1));
					result.AddArgument(static_cast<int>(val2));
				}
				else if (token.equals_ci("round"))
				{
					val = my_round(val1);
					result.SetNameAndResult("round", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("sin"))
				{
					val = std::sin(val1);
					result.SetNameAndResult("sin", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("sinh"))
				{
					val = std::sinh(val1);
					result.SetNameAndResult("sinh", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("sqrt"))
				{
					if (val1 < 0)
					{
						data.errCode = DICE_ERROR_UNDEFINED;
						return 0;
					}
					val = std::sqrt(val1);
					result.SetNameAndResult("sqrt", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("tan"))
				{
					if (!std::fmod(val1 + 2 * std::atan(1.0), std::atan(1.0) * 4))
					{
						data.errCode = DICE_ERROR_UNDEFINED;
						return 0;
					}
					val = std::tan(val1);
					result.SetNameAndResult("tan", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("tanh"))
				{
					val = std::tanh(val1);
					result.SetNameAndResult("tanh", val);
					result.AddArgument(val1);
				}
				else if (token.equals_ci("trunc"))
				{
					val = static_cast<int>(val1);
					result.SetNameAndResult("trunc", val);
					result.AddArgument(val1);
				}
				if (is_infinite(val) || is_notanumber(val))
				{
					data.errCode = is_infinite(val) ? DICE_ERROR_OVERUNDERFLOW : DICE_ERROR_UNDEFINED;
					return 0;
				}
				num_stack.push(val);
				data.AddToOpResults(result);
			}
			else if (is_operator(token[0]) && token.length() == 1)
			{
				if (num_stack.empty() || num_stack.size() < 2)
				{
					data.errCode = DICE_ERROR_STACK;
					data.errStr = "Not enough numbers for operator.";
					return 0;
				}
				double val2 = num_stack.top();
				num_stack.pop();
				double val1 = num_stack.top();
				num_stack.pop();
				switch (token[0])
				{
					case '+':
						val = val1 + val2;
						break;
					case '-':
						val = val1 - val2;
						break;
					case '*':
						val = val1 * val2;
						break;
					case '/':
						if (!val2)
						{
							data.errCode = DICE_ERROR_DIV0;
							return 0;
						}
						val = val1 / val2;
						break;
					case '%':
						if (!val2)
						{
							data.errCode = DICE_ERROR_DIV0;
							return 0;
						}
						val = std::fmod(val1, val2);
						break;
					case '^':
						if (val1 < 0 && static_cast<int>(val2) != val2)
						{
							data.errCode = DICE_ERROR_UNDEFINED;
							return 0;
						}
						if (!val1 && !val2)
						{
							data.errCode = DICE_ERROR_DIV0;
							return 0;
						}
						if (!val1 && val2 < 0)
						{
							data.errCode = DICE_ERROR_OVERUNDERFLOW;
							return 0;
						}
						val = std::pow(val1, val2);
						break;
					case 'd':
					{
						if (val1 < 1 || val1 > DICE_MAX_DICE)
						{
							data.errCode = DICE_ERROR_UNACCEPTABLE_DICE;
							data.errNum = static_cast<int>(val1);
							return 0;
						}
						if (val2 < 1 || val2 > DICE_MAX_SIDES)
						{
							data.errCode = DICE_ERROR_UNACCEPTABLE_SIDES;
							data.errNum = static_cast<int>(val2);
							return 0;
						}
						DiceResult result = Dice(static_cast<int>(val1), static_cast<unsigned>(val2));
						data.AddToOpResults(result);
						val = result.Value();
					}
				}
				if (is_infinite(val) || is_notanumber(val))
				{
					data.errCode = is_infinite(val) ? DICE_ERROR_OVERUNDERFLOW : DICE_ERROR_UNDEFINED;
					return 0;
				}
				num_stack.push(val);
			}
		}
		else
		{
			const PostfixValueDouble *dbl = dynamic_cast<const PostfixValueDouble *>(postfix[x]);
			const double *val_ptr = dbl->Get();
			if (!val_ptr)
			{
				data.errCode = DICE_ERROR_STACK;
				data.errStr = "An empty number was found.";
				return 0;
			}
			num_stack.push(*val_ptr);
		}
	}
	val = num_stack.top();
	num_stack.pop();
	if (!num_stack.empty())
	{
		data.errCode = DICE_ERROR_STACK;
		data.errStr = "Too many numbers were found as input.";
		return 0;
	}
	return val;
}

/** Parse an infix notation expression and convert the expression to postfix notation.
 * @param infix The original expression, in infix notation, to convert to postfix notation
 * @return A postfix notation expression equivilent to the infix notation expression given, or an empty object if the infix notation expression could not be parsed or converted
 */
static Postfix DoParse(DiceServData &data, const Anope::string &infix)
{
	Infix infixcpy = FixInfix(infix);
	Postfix postfix;
	if (infixcpy.str.empty())
		return postfix;
	if (!CheckInfix(data, infixcpy))
		return postfix;
	Infix tokenized_infix = TokenizeInfix(infixcpy);
	if (tokenized_infix.str.empty())
		return postfix;
	postfix = InfixToPostfix(data, tokenized_infix);
	return postfix;
}

/** Evaluate a postfix notation expression.
 * @param postfix The postfix notation expression to evaluate
 * @return The final result after evaluation
 */
static double DoEvaluate(DiceServData &data, const Postfix &postfix)
{
	double ret = EvaluatePostfix(data, postfix);
	if (ret > std::numeric_limits<int>::max() || ret < std::numeric_limits<int>::min())
		data.errCode = DICE_ERROR_OVERUNDERFLOW;
	return ret;
}

const OperatorResultType &OperatorResultBase::Type() const
{
	return this->type;
}

void DiceResult::AddResult(unsigned result)
{
	this->results.push_back(result);
}

const std::vector<unsigned> &DiceResult::Results() const
{
	return this->results;
}

const unsigned &DiceResult::Sides() const
{
	return this->sides;
}

Anope::string DiceResult::DiceString() const
{
	return stringify(this->num) + "d" + stringify(this->sides);
}

unsigned DiceResult::Sum() const
{
	return std::accumulate(this->results.begin(), this->results.end(), 0u);
}

double DiceResult::Value() const
{
	return this->Sum();
}

Anope::string DiceResult::LongString() const
{
	std::ostringstream str;
	str << stringify(this->num) << "d" << stringify(this->sides) << "=(";
	bool first = true;
	for (size_t i = 0, len = this->results.size(); i < len; ++i)
	{
		if (!first)
			str << " ";
		str << stringify(this->results[i]);
		first = false;
	}
	str << ")";
	return str.str();
}

Anope::string DiceResult::ShortString() const
{
	return stringify(this->num) + "d" + stringify(this->sides) + "=(" + stringify(this->Sum()) + ")";
}

DiceResult *DiceResult::Clone() const
{
	return new DiceResult(*this);
}

FunctionResult::FunctionResult(const Anope::string &Name, double Result) : OperatorResultBase(OPERATOR_RESULT_TYPE_FUNCTION), name(Name), arguments(),
	result(Result)
{
}

void FunctionResult::SetNameAndResult(const Anope::string &Name, double Result)
{
	this->name = Name;
	this->result = Result;
}

void FunctionResult::AddArgument(double arg)
{
	this->arguments.push_back(arg);
}

double FunctionResult::Value() const
{
	return this->result;
}

Anope::string FunctionResult::LongString() const
{
	std::ostringstream str;
	str << this->name << "(";
	bool first = true;
	for (size_t i = 0, len = this->arguments.size(); i < len; ++i)
	{
		if (!first)
			str << ",";
		str << stringify(this->arguments[i]);
		first = false;
	}
	str << ")=" << this->result;
	return str.str();
}

Anope::string FunctionResult::ShortString() const
{
	return this->LongString();
}

FunctionResult *FunctionResult::Clone() const
{
	return new FunctionResult(*this);
}

OperatorResults &OperatorResults::operator=(const OperatorResults &other)
{
	if (this != &other)
	{
		this->clear();
		this->append(other);
	}
	return *this;
}

void OperatorResults::add(const DiceResult &result)
{
	this->results.push_back(new DiceResult(result));
}

void OperatorResults::add(const FunctionResult &result)
{
	this->results.push_back(new FunctionResult(result));
}

void OperatorResults::append(const OperatorResults &other)
{
	for (unsigned y = 0, count = other.results.size(); y < count; ++y)
		this->results.push_back(other.results[y]->Clone());
}

bool OperatorResults::empty() const
{
	return this->results.empty();
}

void DiceServData::Reset()
{
	this->timesResults.clear();
	this->opResults.clear();
	this->results.clear();
	this->errCode = DICE_ERROR_NONE;
	this->errStr = "";
	this->errPos = 0u;
	this->errNum = 0;
}

static Anope::string Join(const std::vector<Anope::string> &params, size_t firstParam, size_t lastParam, const Anope::string &delimiter = " ")
{
	Anope::string joinedString;
	for (size_t x = firstParam; x <= lastParam; ++x)
		joinedString += " " + params[x];
	joinedString.erase(0 ,1);
	return joinedString;
}

bool DiceServData::PreParse(CommandSource &source, const std::vector<Anope::string> &params, unsigned expectedChannelPos)
{
	User *user = source.GetUser();
	// Check for a ignore on the user or their registered nick, if any, and deny them access if they are ignored
	if (this->DiceServ->IsIgnored(user))
		return false;
	if (source.GetAccount() && this->DiceServ->IsIgnored(source.GetAccount()))
		return false;
	// Set up the dice, chan, and comment strings
	if (source.c)
	{
		this->chanStr = params[0];
		this->diceStr = params[1];
		if (expectedChannelPos != 1)
			this->extraStr = Join(params, 2, expectedChannelPos);
		this->commentStr = params.size() > expectedChannelPos + 1 ? params[expectedChannelPos + 1] : "";
		this->sourceIsBot = true;
	}
	else
	{
		this->diceStr = params[0];
		if (expectedChannelPos != 1)
			this->extraStr = Join(params, 1, expectedChannelPos - 1);
		this->chanStr = params.size() > expectedChannelPos ? params[expectedChannelPos] : "";
		this->commentStr = params.size() > expectedChannelPos + 1 ? params[expectedChannelPos + 1] : "";
		this->sourceIsBot = false;
	}
	// If the channel doesn't start with #, we'll treat it as if it was part of the comment
	if (!this->chanStr.empty() && this->chanStr[0] != '#')
	{
		this->commentStr = this->chanStr + (this->commentStr.empty() ? "" : " ") + this->commentStr;
		this->chanStr = "";
	}
	/* If a channel was given, ignore the roll if the user isn't in the channel.
	 * Also, check if the channel has ignored rolls to it or if it's been moderated (+m) and the user has no status to the channel. */
	if (!this->chanStr.empty())
	{
		Channel *c = source.c ? *source.c : Channel::Find(this->chanStr);
		if (c)
		{
			if (!c->FindUser(user))
			{
				if (!source.c)
					source.Reply(CHAN_X_INVALID, this->chanStr.c_str());
				return false;
			}
			if (this->DiceServ->IsIgnored(c) || (c->ci ? this->DiceServ->IsIgnored(c->ci) : false) || c->HasUserStatus(user, "MODERATED"))
				this->chanStr = "";
			if (this->chanStr.empty() && source.c)
				return false;
		}
		else
			this->chanStr = "";
	}
	// If a [ is found in the dice expression and the expression ends in a ], assume it is of an alternate group format of x[y] and convert to the x~y format instead
	size_t sbracket = this->diceStr.find('[');
	if (sbracket != Anope::string::npos && this->diceStr[this->diceStr.length() - 1] == ']')
	{
		this->diceStr.erase(this->diceStr.end() - 1);
		this->diceStr[sbracket] = '~';
	}
	size_t tilde = this->diceStr.find('~');
	if (tilde != Anope::string::npos)
	{
		this->timesPart = this->diceStr.substr(0, tilde);
		this->dicePart = this->diceStr.substr(tilde + 1);
	}
	else
		this->dicePart = this->diceStr;
	return true;
}

bool DiceServData::CheckMessageLengthPreProcess(CommandSource &source)
{
	this->maxMessageLength = 510;
	// The following parts are not going to be in the output string generated by DiceServ, but need to be checked anyways.
	BotInfo *bi = source.c ? *source.service : Config->GetClient("DiceServ");
	this->maxMessageLength -= bi->nick.length();
	this->maxMessageLength -= bi->GetIdent().length();
	this->maxMessageLength -= bi->host.length();
	this->maxMessageLength -= 7; // For the :, !, and @, plus the space after that and after the PRIVMSG/NOTICE and after the target and the : for the message
	this->maxMessageLength -= !this->chanStr.empty() && this->sourceIsBot ? 7 : 6; // inchan with BotServ bot == PRIVMSG, otherwise NOTICE
	this->maxMessageLength -= !this->chanStr.empty() ? this->chanStr.length() : source.GetUser()->nick.length(); // inchan uses channel's name, otherwise uses user's nick
	// The following parts are going to be in the output string generated by DiceServ, so don't modify the member variable.
	int restMaxMessageLength = this->maxMessageLength;
	restMaxMessageLength -= 7; // For the < > [ ] :, and the space before the [ and after the :
	if (!this->rollPrefix.empty())
		restMaxMessageLength -= this->rollPrefix.length(); // The prefix of the roll string itself
	if (!this->dicePrefix.empty())
		restMaxMessageLength -= this->dicePrefix.length(); // The prefix of the dice expression
	restMaxMessageLength -= this->diceStr.length(); // The dice expression itself
	if (!this->diceSuffix.empty())
		restMaxMessageLength -= this->diceSuffix.length(); // The suffix of the dice expression
	if (!this->chanStr.empty())
	{
		restMaxMessageLength -= 4; // "for "
		restMaxMessageLength -= source.GetUser()->nick.length(); // nick of user who used the command
	}
	if (!this->commentStr.empty())
		restMaxMessageLength -= this->commentStr.length() + 1; // Comment plus space
	// Check for overflow prior to adding in dice results
	if (restMaxMessageLength <= 0)
	{
		source.Reply(_("Dice result buffer has an overflow. This could be due to\n"
			"large values that are close to the limits or the size of\n"
			"your comment. Please enter some lower rolls or a smaller\n"
			"comment."));
		return false;
	}
	return true;
}

bool DiceServData::CheckMessageLengthPostProcess(CommandSource &source, const Anope::string &output) const
{
	if (this->maxMessageLength - static_cast<int>(output.length()) <= 0)
	{
		source.Reply(_("Dice result buffer has an overflow. This could be due to\n"
			"large values that are close to the limits or the size of\n"
			"your comment. Please enter some lower rolls or a smaller\n"
			"comment."));
		return false;
	}
	return true;
}

Anope::string DiceServData::GenerateLongExOutput() const
{
	std::ostringstream output;
	output << "<" << this->rollPrefix << " [" << this->dicePrefix << this->diceStr << this->diceSuffix << "]: ";

	if (this->isExtended)
	{
		if (!this->timesResults.empty() || !this->opResults.empty())
			output << "{";

		if (!this->timesResults.empty())
		{
			bool first = true;
			for (size_t i = 0, len = this->timesResults.size(); i < len; ++i)
			{
				if (!first)
					output << " ";
				output << this->timesResults[i]->LongString();
				first = false;
			}

			output << " ~ ";
		}
		if (!this->opResults.empty())
		{
			bool firstOp = true;

			for (size_t i = 0, len = this->opResults.size(); i < len; ++i)
			{
				if (!firstOp)
					output << " | ";
				bool first = true;
				for (size_t j = 0, len2 = this->opResults[i].size(); j < len2; ++j)
				{
					if (!first)
						output << " ";
					output << this->opResults[i][j]->LongString();
					first = false;
				}
				firstOp = false;
			}
		}

		if (!this->timesResults.empty() || !this->opResults.empty())
			output << "} ";
	}

	bool first = true;
	for (size_t i = 0, len = this->results.size(); i < len; ++i)
	{
		if (!first)
			output << " ";
		output << stringify(this->results[i]);
		first = false;
	}

	output << ">";
	if (!this->commentStr.empty())
		output << " " << this->commentStr;

	return output.str();
}

Anope::string DiceServData::GenerateShortExOutput() const
{
	std::ostringstream output;
	output << "<" << this->rollPrefix << " [" << this->dicePrefix << this->diceStr << this->diceSuffix << "]: ";

	if (this->isExtended)
	{
		if (!this->timesResults.empty() || !this->opResults.empty())
			output << "{";

		if (!this->timesResults.empty())
		{
			bool first = true;
			for (size_t i = 0, len = this->timesResults.size(); i < len; ++i)
			{
				if (!first)
					output << " ";
				output << this->timesResults[i]->ShortString();
				first = false;
			}

			output << " ~ ";
		}
		if (!this->opResults.empty())
		{
			bool firstOp = true;

			for (size_t i = 0, len = this->opResults.size(); i < len; ++i)
			{
				if (!firstOp)
					output << " | ";
				bool first = true;
				for (size_t j = 0, len2 = this->opResults[i].size(); j < len2; ++j)
				{
					if (!first)
						output << " ";
					output << this->opResults[i][j]->ShortString();
					first = false;
				}
				firstOp = false;
			}
		}

		if (!this->timesResults.empty() || !this->opResults.empty())
			output << "} ";
	}

	bool first = true;
	for (size_t i = 0, len = this->results.size(); i < len; ++i)
	{
		if (!first)
			output << " ";
		output << stringify(this->results[i]);
		first = false;
	}

	output << ">";
	if (!this->commentStr.empty())
		output << " " << this->commentStr;

	return output.str();
}

Anope::string DiceServData::GenerateNoExOutput() const
{
	std::ostringstream output;
	output << "<" << this->rollPrefix << " [" << this->dicePrefix << this->diceStr << this->diceSuffix << "]: ";

	bool first = true;
	for (size_t i = 0, len = this->results.size(); i < len; ++i)
	{
		if (!first)
			output << " ";
		output << stringify(this->results[i]);
		first = false;
	}

	output << ">";
	if (!this->commentStr.empty())
		output << " " << this->commentStr;

	return output.str();
}

void DiceServData::StartNewOpResults()
{
	this->opResults.push_back(OperatorResults());
}

void DiceServData::AddToOpResults(const DiceResult &result)
{
	this->opResults[this->opResults.size() - 1].add(result);
}

void DiceServData::AddToOpResults(const FunctionResult &result)
{
	this->opResults[this->opResults.size() - 1].add(result);
}

void DiceServData::SetOpResultsAsTimesResults()
{
	this->timesResults = this->opResults[0];
	this->opResults.clear();
}

void DiceServData::Roll()
{
	this->DiceServ->Roller(*this);
}

DiceResult *DiceServData::Dice(int num, unsigned sides)
{
	return this->DiceServ->Dice(num, sides);
}

void DiceServData::HandleError(CommandSource &source)
{
	this->DiceServ->ErrorHandler(source, *this);
}

void DiceServData::SendReply(CommandSource &source, const Anope::string &output) const
{
	if (this->chanStr.empty())
		source.Reply(output);
	else if (this->sourceIsBot)
		IRCD->SendPrivmsg(*source.service, this->chanStr, "%s", output.c_str());
	else
		IRCD->SendNotice(Config->GetClient("DiceServ"), this->chanStr, "%s", output.c_str());
}

/** A middleman service to prevent the need for most of DiceServData's code being in the header (and thus only defined once here in the core).
 */
class DiceServDataHandler : public DiceServDataHandlerService
{
public:
	DiceServDataHandler(Module *m) : DiceServDataHandlerService(m)
	{
	}

	void Reset(DiceServData &data)
	{
		data.Reset();
	}

	bool PreParse(DiceServData &data, CommandSource &source, const std::vector<Anope::string> &params, unsigned expectedChannelPos)
	{
		return data.PreParse(source, params, expectedChannelPos);
	}

	bool CheckMessageLengthPreProcess(DiceServData &data, CommandSource &source)
	{
		return data.CheckMessageLengthPreProcess(source);
	}

	bool CheckMessageLengthPostProcess(const DiceServData &data, CommandSource &source, const Anope::string &output) const
	{
		return data.CheckMessageLengthPostProcess(source, output);
	}

	Anope::string GenerateLongExOutput(const DiceServData &data) const
	{
		return data.GenerateLongExOutput();
	}

	Anope::string GenerateShortExOutput(const DiceServData &data) const
	{
		return data.GenerateShortExOutput();
	}

	Anope::string GenerateNoExOutput(const DiceServData &data) const
	{
		return data.GenerateNoExOutput();
	}

	void StartNewOpResults(DiceServData &data)
	{
		data.StartNewOpResults();
	}

	void AddToOpResults(DiceServData &data, const DiceResult &result)
	{
		data.AddToOpResults(result);
	}

	void AddToOpResults(DiceServData &data, const FunctionResult &result)
	{
		data.AddToOpResults(result);
	}

	void SetOpResultsAsTimesResults(DiceServData &data)
	{
		data.SetOpResultsAsTimesResults();
	}

	void Roll(DiceServData &data)
	{
		data.Roll();
	}

	DiceResult *Dice(DiceServData &data, int num, unsigned sides)
	{
		return data.Dice(num, sides);
	}

	void HandleError(DiceServData &data, CommandSource &source)
	{
		data.HandleError(source);
	}

	void SendReply(const DiceServData &data, CommandSource &source, const Anope::string &output) const
	{
		data.SendReply(source, output);
	}

	const std::vector<unsigned> &Results(const DiceResult &result) const
	{
		return result.Results();
	}

	const unsigned &Sides(const DiceResult &result) const
	{
		return result.Sides();
	}

	Anope::string DiceString(const DiceResult &result) const
	{
		return result.DiceString();
	}

	unsigned Sum(const DiceResult &result) const
	{
		return result.Sum();
	}

	DiceResult *Clone(const DiceResult &result) const
	{
		return result.Clone();
	}
};

/** A timer designed to load an old DiceServ database from Anope 1.8.x or pre-Anope 1.9.2 after the main database has loaded.
 */
class DiceServUpgradeTimer : public Timer
{
	Anope::string diceservdb;

public:
	DiceServUpgradeTimer(Module *creator, long timeout, bool dorepeat, const Anope::string &db) : Timer(creator, timeout, Anope::CurTime, dorepeat), diceservdb(db)
	{
	}

	void Tick(time_t) anope_override;
};

/** DiceServ's core module, provides the interface for other modules to be able to use the roller.
 */
class DiceServCore : public Module, public DiceServService
{
	Reference<BotInfo> DiceServ;
	DiceServDataHandler DiceServHandler;
	SerializableExtensibleItem<bool> DiceServIgnore;

	/** Makes sure that a user who was ignored by their NickServ account is still ignored no matter what.
	 */
	void NickEvent(User *u)
	{
		if (u->Account() && this->IsIgnored(u->Account()))
			this->Ignore(u);
	}

public:
	DiceServCore(const Anope::string &modname, const Anope::string &creator) : Module(modname, creator, PSEUDOCLIENT | THIRD), DiceServService(this),
		DiceServHandler(this), DiceServIgnore(this, "diceserv_ignore")
	{
		this->SetAuthor(DiceServService::Author());
		this->SetVersion(DiceServService::Version());

		const Anope::string &diceservdb = Config->GetModule(this)->Get<const Anope::string>("diceservdb", "");
		if (!diceservdb.empty())
		{
			std::ifstream oldDatabase(diceservdb.c_str(), std::ios::in | std::ios::binary);

			if (oldDatabase)
			{
				oldDatabase.close();

				if (Me->IsSynced())
					new DiceServUpgradeTimer(this, 0, false, diceservdb);
				else
					new DiceServUpgradeTimer(this, 1, true, diceservdb);
			}
		}
	}

	void OnReload(Configuration::Conf *conf) anope_override
	{
		const Anope::string &dsnick = conf->GetModule(this)->Get<const Anope::string>("client", "DiceServ");
		this->DiceServ = BotInfo::Find(dsnick, true);
	}

	/** Handles accessing HELP FUNCTIONS
	 */
	EventReturn OnPreCommand(CommandSource &source, Command *command, std::vector<Anope::string> &params)
	{
		if (command->name.equals_ci("generic/help"))
		{
			Anope::string help = params.size() ? params[0] : "";

			if (help.equals_ci("FUNCTIONS"))
			{
				source.Reply(_("%s recognizes the following functions:\n"
					" \n"
					"    abs(\037x\037)         Absolute value of \037x\037\n"
					"    acos(\037x\037)        Arc cosine of \037x\037\n"
					"    acosh(\037x\037)       Inverse hyperbolic cosine of \037x\037\n"
					"    asin(\037x\037)        Arc sine of \037x\037\n"
					"    asinh(\037x\037)       Inverse hyperbolic sine of \037x\037\n"
					"    atan(\037x\037)        Arc tangent of \037x\037\n"
					"    atan2(\037y\037,\037x\037)     Arc tangent of \037y\037/\037x\037\n"
					"    atanh(\037x\037)       Inverse hyperbolic tangent of \037x\037\n"
					"    cbrt(\037x\037)        Cube root of \037x\037\n"
					"    ceil(\037x\037)        The next smallest integer greater than\n"
					"                   or equal to \037x\037\n"
					"    cos(\037x\037)         Cosine of \037x\037\n"
					"    cosh(\037x\037)        Hyperbolic cosine of \037x\037\n"
					"    deg(\037x\037)         Convert \037x\037 from radians to degrees\n"
					"    exp(\037x\037)         e (exponential value) to the power\n"
					"                   of \037x\037\n"
					"    fac(\037x\037)         Factorial of \037x\037\n"
					"    floor(\037x\037)       The next largest integer less than or\n"
					"                   equal to \037x\037\n"
					"    log(\037x\037)         Natural logarithm of \037x\037\n"
					"    log10(\037x\037)       Commmon logarithm of \037x\037\n"
					"    max(...)       Maximum of all values given (they must\n"
					"                   be separated by commas)\n"
					"    min(...)       Minimum of all values given (they must\n"
					"                   be separated by commas)\n"
					"    rad(\037x\037)         Convert \037x\037 from degrees to radians\n"
					"    rand(\037x\037,\037y\037)      Random value between \037x\037 and \037y\037\n"
					"    round(\037x\037)       Round \037x\037 to the nearest integer\n"
					"    sin(\037x\037)         Sine of \037x\037\n"
					"    sinh(\037x\037)        Hyperbolic sine of \037x\037\n"
					"    sqrt(\037x\037)        Square root of \037x\037\n"
					"    tan(\037x\037)         Tangent of \037x\037\n"
					"    tanh(\037x\037)        Hyperbolic tangent of \037x\037\n"
					"    trunc(\037x\037)       The integral portion of \037x\037\n"
					" \n"
					"NOTE: All trigonometric functions above (sine, cosine and\n"
					"tangent) return their values in radians."), this->DiceServ->nick.c_str());
				return EVENT_STOP;
			}
		}

		return EVENT_CONTINUE;
	}

	/** Handles adding a line for DiceServ status to NS INFO and CS INFO
	 */
	void OnPostCommand(CommandSource &source, Command *command, const std::vector<Anope::string> &params)
	{
		if (command->name.equals_ci("nickserv/info"))
		{
			Anope::string nick = params.size() ? params[0] : "";

			if (!nick.empty() && source.HasCommand("diceserv/info"))
			{
				NickAlias *na = NickAlias::Find(nick);
				if (na)
					source.Reply(_("%s Status: %s"), this->DiceServ->nick.c_str(), this->IsIgnored(na->nc) ? _("Ignored") : _("Allowed"));
			}
		}
		else if (command->name.equals_ci("chanserv/info"))
		{
			Anope::string chan = params.size() ? params[0] : "";

			if (!chan.empty())
			{
				ChannelInfo *ci = ChannelInfo::Find(chan);
				if (ci && ((ci->HasExt("SECUREFOUNDER") ? source.IsFounder(ci) : source.AccessFor(ci).HasPriv("FOUNDER")) ||
					source.HasCommand("diceserv/info")))
					source.Reply(_("%s Status: %s"), this->DiceServ->nick.c_str(), this->IsIgnored(ci) ? _("Ignored") : _("Allowed"));
			}
		}
	}

	/** Displays the help header for the core of DiceServ.
	 */
	EventReturn OnPreHelp(CommandSource &source, const std::vector<Anope::string> &params) anope_override
	{
		if (*source.service == this->DiceServ && params.empty())
			source.Reply(_("\002%s\002 allows you to roll any number of dice with any\n"
				"number of sides. The output of the roll can either be output\n"
				"just to you, or you can have it notice the result to a\n"
				"channel. Available commands are listed below; to use them,\n"
				"type \002%s%s \037command\037\002. For more information on a\n"
				"specific command, type \002%s%s HELP \037command\037\002.\n"
				" "), this->DiceServ->nick.c_str(), Config->StrictPrivmsg.c_str(), this->DiceServ->nick.c_str(), Config->StrictPrivmsg.c_str(),
				this->DiceServ->nick.c_str());

		return EVENT_CONTINUE;
	}

	/** Displays the help footer for the core of DiceServ.
	 */
	void OnPostHelp(CommandSource &source, const std::vector<Anope::string> &params) anope_override
	{
		if (*source.service == this->DiceServ && params.empty())
		{
			BotInfo *BotServ = Config->GetClient("BotServ");
			source.Reply(_(" \n"
				"\002%s\002 will check for syntax errors and tell you what\n"
				"errors you have.\n"
				" \n"
				"If a %s bot is in a channel, you can also trigger the\n"
				"both within the channel using fantasy commands. If a\n"
				"%s bot is in the channel, output will be said by the\n"
				"bot. Otherwise, it will be said by %s. Syntax of the\n"
				"fantasy commands can be found in the help of each command.\n"
				" \n"
				"%s by Naram Qashat (CyberBotX, cyberbotx@cyberbotx.com).\n"
				"Questions, comments, or concerns can be directed to email or\n"
				"to #DiceServ on jenna.cyberbotx.com."), this->DiceServ->nick.c_str(), BotServ ? BotServ->nick.c_str() : "BotServ",
				BotServ ? BotServ->nick.c_str() : "BotServ", this->DiceServ->nick.c_str(), this->DiceServ->nick.c_str());
		}
	}

	/** Updates the DiceServ ignore status of a user connecting if they were ignored on their NickServ account.
	 */
	void OnUserConnect(User *u, bool &) anope_override
	{
		this->NickEvent(u);
	}

	/** Updates the DiceServ ignore status of a user who's nick was changed if they were ignored on their NickServ account.
	 */
	void OnUserNickChange(User *u, const Anope::string &) anope_override
	{
		this->NickEvent(u);
	}

	/** If a user was ignored in DiceServ when they register a nick, then persist the ignore onto their account.
	 */
	void OnNickRegister(User *u, NickAlias *, const Anope::string &) anope_override
	{
		if (this->IsIgnored(u))
			this->Ignore(u->Account());
	}

	/** Updates the DiceServ ignore status of a channel when someone joins it if it was ignored on its ChanServ account.
	 */
	void OnJoinChannel(User *, Channel *c) anope_override
	{
		if (c->ci && this->IsIgnored(c->ci))
			this->Ignore(c);
	}

	/** If a channel was ignored in DiceServ when it gets registered, then persist the ignore onto the registered channel.
	 */
	void OnChanRegistered(ChannelInfo *ci) anope_override
	{
		if (ci->c && this->IsIgnored(ci->c))
			this->Ignore(ci);
	}

	/** DiceServ error handler, will output an error message to the user if any errors occurred.
	 */
	void ErrorHandler(CommandSource &source, const DiceServData &data)
	{
		switch (data.errCode)
		{
			case DICE_ERROR_NONE:
				break;
			case DICE_ERROR_PARSE:
			{
				source.Reply(_("During parsing, an error was found in the following\nexpression:"));
				source.Reply(" %s", data.diceStr.c_str());
				Anope::string spaces(data.errPos > data.diceStr.length() ? data.diceStr.length() : data.errPos, ' ');
				source.Reply("(%s^)", spaces.c_str());
				source.Reply(_("Error description is as follows:"));
				source.Reply("%s", data.errStr.c_str());
				break;
			}
			case DICE_ERROR_DIV0:
				source.Reply(_("Division by 0 in following expression:"));
				source.Reply(" %s", data.diceStr.c_str());
				break;
			case DICE_ERROR_UNDEFINED:
				source.Reply(_("Undefined result in following expression:"));
				source.Reply(" %s", data.diceStr.c_str());
				break;
			case DICE_ERROR_UNACCEPTABLE_DICE:
				if (data.errNum <= 0)
					source.Reply(_("The number of dice that you entered (\037%d\037) was under\n1. Please enter a number between 1 and %d."), data.errNum,
						DICE_MAX_DICE);
				else
					source.Reply(_("The number of dice that you entered (\037%d\037) was over the\nlimit of %d. Please enter a lower number of dice."),
						data.errNum, DICE_MAX_DICE);
				break;
			case DICE_ERROR_UNACCEPTABLE_SIDES:
				if (data.errNum <= 0)
					source.Reply(_("The number of sides that you entered (\037%d\037) was under\n1. Please enter a number between 1 and %d."), data.errNum,
						DICE_MAX_SIDES);
				else
					source.Reply(_("The number of sides that you entered (\037%d\037) was over the\nlimit of %d. Please enter a lower number of sides."),
						data.errNum, DICE_MAX_SIDES);
				break;
			case DICE_ERROR_UNACCEPTABLE_TIMES:
				if (data.errNum <= 0)
					source.Reply(_("The number of times that you entered (\037%d\037) was under\n1. Please enter a number between 1 and %d."), data.errNum,
						DICE_MAX_TIMES);
				else
					source.Reply(_("The number of times that you entered (\037%d\037) was over the\nlimit of %d. Please enter a lower number of times."),
						data.errNum, DICE_MAX_TIMES);
				break;
			case DICE_ERROR_OVERUNDERFLOW:
				source.Reply(_("Dice results in following expression resulted in either\noverflow or underflow:"));
				source.Reply(" %s", data.diceStr.c_str());
				break;
			case DICE_ERROR_STACK:
				source.Reply(_("The following roll expression could not be properly\nevaluated, please try again or let an administrator know."));
				source.Reply(" %s", data.diceStr.c_str());
				source.Reply(_("Error description is as follows:"));
				source.Reply("%s", data.errStr.c_str());
				break;
		}
	}

	/** DiceServ's core roller, handles parsing the actual expression and then executing it however many times is necessary.
	 */
	void Roller(DiceServData &data)
	{
		double v; // Stores the result of the dice expression
		int n = 1; // Temporary counter for number of sets to roll, defaults to rolling once
		// The following is for handling if there was a given number of times to roll
		if (!data.timesPart.empty())
		{
			if (data.dicePart.empty())
			{
				data.errCode = DICE_ERROR_PARSE;
				data.errStr = "An empty dice expression was found.";
				data.errPos = data.timesPart.length() + 1;
				return;
			}
			Postfix times_postfix = DoParse(data, data.timesPart);
			// If the parsing failed, leave
			if (times_postfix.empty())
				return;
			// Evaulate the expression
			data.StartNewOpResults();
			v = DoEvaluate(data, times_postfix);
			data.SetOpResultsAsTimesResults();
			times_postfix.clear();
			// Check if the evaluated number of times is out of bounds
			if (data.errCode == DICE_ERROR_NONE)
			{
				n = static_cast<int>(v);
				if (n < 1 || n > DICE_MAX_TIMES)
				{
					data.errCode = DICE_ERROR_UNACCEPTABLE_TIMES;
					data.errNum = n;
					return;
				}
			}
		}
		// As long as there was no error, roll the dice
		if (data.errCode == DICE_ERROR_NONE)
		{
			// Parse the dice
			Postfix dice_postfix = DoParse(data, data.dicePart);
			// If the parsing failed, leave
			if (dice_postfix.empty())
			{
				if (!data.timesPart.empty())
					data.errPos += data.timesPart.length() + 1;
				return;
			}
			// Roll as many sets as were requested
			for (; n > 0; --n)
			{
				// Evaluate the dice, then check for errors
				data.StartNewOpResults();
				v = DoEvaluate(data, dice_postfix);
				// As long as we didn't have an error, we will continue
				if (data.errCode == DICE_ERROR_NONE)
					// Round the result and add it the buffer
					data.results.push_back(data.roundResults ? static_cast<int>(my_round(v)) : v);
				// Leave if there was an error
				else
				{
					if (!data.timesPart.empty())
						data.errPos += data.timesPart.length() + 1;
					return;
				}
			}
			dice_postfix.clear();
		}
	}

	/** A middleman function to roll dice, used currently by the Earthdawn command for generating bonus rolls.
	 */
	DiceResult *Dice(int num, unsigned sides)
	{
		return ::Dice(num, sides).Clone();
	}

	/** Add an ignore to the given object (usually a channel or nick).
	 * @param obj The extensible object to add an ignore to.
	 */
	void Ignore(Extensible *obj)
	{
		this->DiceServIgnore.Set(obj);
	}

	/** Remove an ignore from the given object (usually a channel or nick).
	 * @param obj The extensible object to remove an ignore from.
	 */
	void Unignore(Extensible *obj)
	{
		this->DiceServIgnore.Unset(obj);
	}

	/** Get if the given object (usually a channel or nick) is ignored.
	 * @param obj The extensible object to check ignore status of.
	 * @return true if the object is ignored, false otherwise.
	 */
	bool IsIgnored(Extensible *obj)
	{
		return this->DiceServIgnore.HasExt(obj);
	}
};

void DiceServUpgradeTimer::Tick(time_t) anope_override
{
	if (Me->IsSynced())
	{
		DiceServCore *DiceServ = anope_dynamic_static_cast<DiceServCore *>(this->GetOwner());

		std::ifstream oldDatabase(this->diceservdb.c_str(), std::ios::in | std::ios::binary);

		do
		{
			std::string line;
			getline(oldDatabase, line);

			if (oldDatabase.eof())
				break;

			spacesepstream sep(line);
			Anope::string ignore_type, ignore_name;
			sep.GetToken(ignore_type);
			sep.GetToken(ignore_name);
			if (!ignore_type.empty() && !ignore_name.empty())
			{
				if (ignore_type.equals_ci("C"))
				{
					ChannelInfo *ci = ChannelInfo::Find(ignore_name);
					if (ci)
						DiceServ->Ignore(ci);
				}
				else if (ignore_type.equals_ci("N"))
				{
					NickAlias *na = NickAlias::Find(ignore_name);
					if (na)
						DiceServ->Ignore(na->nc);
				}
			}
		} while (true);

		oldDatabase.close();

		unlink(this->diceservdb.c_str());

		Log(DiceServ) << "Loaded old database, it has been deleted and ignore data will now be stored as metadata in main database. Please comment out the diceservdb directive in the diceserv module configuration block.";

		if (this->GetRepeat())
			delete this;
	}
}

MODULE_INIT(DiceServCore)
