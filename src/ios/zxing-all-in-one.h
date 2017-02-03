#include <map>
#include <exception>
#include <algorithm>
#include <typeinfo>
#include <string>
#include <limits>
#include <limits.h>
#include <sstream>
#include <cstdarg>
#include <math.h>
#include <vector>
#include <cmath>
#include <string.h>
#include <memory>
#include <cstdlib>
#include <iostream>
#include <stdlib.h>
#include <iconv.h>

// some specials for QR-codes
#define kPrefixBinary "#LSAD" // after the prefix comes *real* binary data (to be taken as is and to be base64 encoded)
                              // has to at least end with alphanumerics, so the QR-Code is multi-part
#ifdef kPrefixBinary
#define kPrefixLength 7 // total prefix-lenght can be more, e.g. with "#LSAD01" or "#LSAD02" for sub-types
#endif

// file: /bigint/NumberlikeArray.hh

#ifndef NUMBERLIKEARRAY_H
#define NUMBERLIKEARRAY_H

// Make sure we have NULL.
#ifndef NULL
#define NULL 0
#endif

/* A NumberlikeArray<Blk> object holds a heap-allocated array of Blk with a
 * length and a capacity and provides basic memory management features.
 * BigUnsigned and BigUnsignedInABase both subclass it.
 *
 * NumberlikeArray provides no information hiding.  Subclasses should use
 * nonpublic inheritance and manually expose members as desired using
 * declarations like this:
 *
 * public:
 *     NumberlikeArray< the-type-argument >::getLength;
 */
template <class Blk>
class NumberlikeArray {
public:
    
    // Type for the index of a block in the array
    typedef unsigned int Index;
    // The number of bits in a block, defined below.
    static const unsigned int N;
    
    // The current allocated capacity of this NumberlikeArray (in blocks)
    Index cap;
    // The actual length of the value stored in this NumberlikeArray (in blocks)
    Index len;
    // Heap-allocated array of the blocks (can be NULL if len == 0)
    Blk *blk;
    
    // Constructs a ``zero'' NumberlikeArray with the given capacity.
    NumberlikeArray(Index c) : cap(c), len(0) {
        blk = (cap > 0) ? (new Blk[cap]) : NULL;
    }
    
    /* Constructs a zero NumberlikeArray without allocating a backing array.
     * A subclass that doesn't know the needed capacity at initialization
     * time can use this constructor and then overwrite blk without first
     * deleting it. */
    NumberlikeArray() : cap(0), len(0) {
        blk = NULL;
    }
    
    // Destructor.  Note that `delete NULL' is a no-op.
    ~NumberlikeArray() {
        delete [] blk;
    }
    
    /* Ensures that the array has at least the requested capacity; may
     * destroy the contents. */
    void allocate(Index c);
    
    /* Ensures that the array has at least the requested capacity; does not
     * destroy the contents. */
    void allocateAndCopy(Index c);
    
    // Copy constructor
    NumberlikeArray(const NumberlikeArray<Blk> &x);
    
    // Assignment operator
    void operator=(const NumberlikeArray<Blk> &x);
    
    // Constructor that copies from a given array of blocks
    NumberlikeArray(const Blk *b, Index blen);
    
    // ACCESSORS
    Index getCapacity()     const { return cap;      }
    Index getLength()       const { return len;      }
    Blk   getBlock(Index i) const { return blk[i];   }
    bool  isEmpty()         const { return len == 0; }
    
    /* Equality comparison: checks if both objects have the same length and
     * equal (==) array elements to that length.  Subclasses may wish to
     * override. */
    bool operator ==(const NumberlikeArray<Blk> &x) const;
    
    bool operator !=(const NumberlikeArray<Blk> &x) const {
        return !operator ==(x);
    }
};

/* BEGIN TEMPLATE DEFINITIONS.  They are present here so that source files that
 * include this header file can generate the necessary real definitions. */

template <class Blk>
const unsigned int NumberlikeArray<Blk>::N = 8 * sizeof(Blk);

template <class Blk>
void NumberlikeArray<Blk>::allocate(Index c) {
    // If the requested capacity is more than the current capacity...
    if (c > cap) {
        // Delete the old number array
        delete [] blk;
        // Allocate the new array
        cap = c;
        blk = new Blk[cap];
    }
}

template <class Blk>
void NumberlikeArray<Blk>::allocateAndCopy(Index c) {
    // If the requested capacity is more than the current capacity...
    if (c > cap) {
        Blk *oldBlk = blk;
        // Allocate the new number array
        cap = c;
        blk = new Blk[cap];
        // Copy number blocks
        Index i;
        for (i = 0; i < len; i++)
            blk[i] = oldBlk[i];
        // Delete the old array
        delete [] oldBlk;
    }
}

template <class Blk>
NumberlikeArray<Blk>::NumberlikeArray(const NumberlikeArray<Blk> &x)
: len(x.len) {
    // Create array
    cap = len;
    blk = new Blk[cap];
    // Copy blocks
    Index i;
    for (i = 0; i < len; i++)
        blk[i] = x.blk[i];
}

template <class Blk>
void NumberlikeArray<Blk>::operator=(const NumberlikeArray<Blk> &x) {
    /* Calls like a = a have no effect; catch them before the aliasing
     * causes a problem */
    if (this == &x)
        return;
    // Copy length
    len = x.len;
    // Expand array if necessary
    allocate(len);
    // Copy number blocks
    Index i;
    for (i = 0; i < len; i++)
        blk[i] = x.blk[i];
}

template <class Blk>
NumberlikeArray<Blk>::NumberlikeArray(const Blk *b, Index blen)
: cap(blen), len(blen) {
    // Create array
    blk = new Blk[cap];
    // Copy blocks
    Index i;
    for (i = 0; i < len; i++)
        blk[i] = b[i];
}

template <class Blk>
bool NumberlikeArray<Blk>::operator ==(const NumberlikeArray<Blk> &x) const {
    if (len != x.len)
        // Definitely unequal.
        return false;
    else {
        // Compare corresponding blocks one by one.
        Index i;
        for (i = 0; i < len; i++)
            if (blk[i] != x.blk[i])
                return false;
        // No blocks differed, so the objects are equal.
        return true;
    }
}

#endif

// file: /bigint/BigUnsigned.hh

#ifndef BIGUNSIGNED_H
#define BIGUNSIGNED_H

// #include "NumberlikeArray.hh"

/* A BigUnsigned object represents a nonnegative integer of size limited only by
 * available memory.  BigUnsigneds support most mathematical operators and can
 * be converted to and from most primitive integer types.
 *
 * The number is stored as a NumberlikeArray of unsigned longs as if it were
 * written in base 256^sizeof(unsigned long).  The least significant block is
 * first, and the length is such that the most significant block is nonzero. */
class BigUnsigned : protected NumberlikeArray<unsigned long> {

public:
	// Enumeration for the result of a comparison.
	enum CmpRes { less = -1, equal = 0, greater = 1 };

	// BigUnsigneds are built with a Blk type of unsigned long.
	typedef unsigned long Blk;

	typedef NumberlikeArray<Blk>::Index Index;
	using NumberlikeArray<Blk>::N;

protected:
	// Creates a BigUnsigned with a capacity; for internal use.
	BigUnsigned(int, Index c) : NumberlikeArray<Blk>(0, c) {}

	// Decreases len to eliminate any leading zero blocks.
	void zapLeadingZeros() {
		while (len > 0 && blk[len - 1] == 0)
			len--;
	}

public:
	// Constructs zero.
	BigUnsigned() : NumberlikeArray<Blk>() {}

	// Copy constructor
	BigUnsigned(const BigUnsigned &x) : NumberlikeArray<Blk>(x) {}

	// Assignment operator
	void operator=(const BigUnsigned &x) {
		NumberlikeArray<Blk>::operator =(x);
	}

	// Constructor that copies from a given array of blocks.
	BigUnsigned(const Blk *b, Index blen) : NumberlikeArray<Blk>(b, blen) {
		// Eliminate any leading zeros we may have been passed.
		zapLeadingZeros();
	}

	// Destructor.  NumberlikeArray does the delete for us.
	~BigUnsigned() {}

	// Constructors from primitive integer types
	BigUnsigned(unsigned long  x);
	BigUnsigned(         long  x);
	BigUnsigned(unsigned int   x);
	BigUnsigned(         int   x);
	BigUnsigned(unsigned short x);
	BigUnsigned(         short x);
protected:
	// Helpers
	template <class X> void initFromPrimitive      (X x);
	template <class X> void initFromSignedPrimitive(X x);
public:

	/* Converters to primitive integer types
	 * The implicit conversion operators caused trouble, so these are now
	 * named. */
	unsigned long  toUnsignedLong () const;
	long           toLong         () const;
	unsigned int   toUnsignedInt  () const;
	int            toInt          () const;
	unsigned short toUnsignedShort() const;
	short          toShort        () const;
protected:
	// Helpers
	template <class X> X convertToSignedPrimitive() const;
	template <class X> X convertToPrimitive      () const;
public:

	// BIT/BLOCK ACCESSORS

	// Expose these from NumberlikeArray directly.
	using NumberlikeArray<Blk>::getCapacity;
	using NumberlikeArray<Blk>::getLength;

	/* Returns the requested block, or 0 if it is beyond the length (as if
	 * the number had 0s infinitely to the left). */
	Blk getBlock(Index i) const { return i >= len ? 0 : blk[i]; }
	/* Sets the requested block.  The number grows or shrinks as necessary. */
	void setBlock(Index i, Blk newBlock);

	// The number is zero if and only if the canonical length is zero.
	bool isZero() const { return NumberlikeArray<Blk>::isEmpty(); }

	/* Returns the length of the number in bits, i.e., zero if the number
	 * is zero and otherwise one more than the largest value of bi for
	 * which getBit(bi) returns true. */
	Index bitLength() const;
	/* Get the state of bit bi, which has value 2^bi.  Bits beyond the
	 * number's length are considered to be 0. */
	bool getBit(Index bi) const {
		return (getBlock(bi / N) & (Blk(1) << (bi % N))) != 0;
	}
	/* Sets the state of bit bi to newBit.  The number grows or shrinks as
	 * necessary. */
	void setBit(Index bi, bool newBit);

	// COMPARISONS

	// Compares this to x like Perl's <=>
	CmpRes compareTo(const BigUnsigned &x) const;

	// Ordinary comparison operators
	bool operator ==(const BigUnsigned &x) const {
		return NumberlikeArray<Blk>::operator ==(x);
	}
	bool operator !=(const BigUnsigned &x) const {
		return NumberlikeArray<Blk>::operator !=(x);
	}
	bool operator < (const BigUnsigned &x) const { return compareTo(x) == less   ; }
	bool operator <=(const BigUnsigned &x) const { return compareTo(x) != greater; }
	bool operator >=(const BigUnsigned &x) const { return compareTo(x) != less   ; }
	bool operator > (const BigUnsigned &x) const { return compareTo(x) == greater; }

	/*
	 * BigUnsigned and BigInteger both provide three kinds of operators.
	 * Here ``big-integer'' refers to BigInteger or BigUnsigned.
	 *
	 * (1) Overloaded ``return-by-value'' operators:
	 *     +, -, *, /, %, unary -, &, |, ^, <<, >>.
	 * Big-integer code using these operators looks identical to code using
	 * the primitive integer types.  These operators take one or two
	 * big-integer inputs and return a big-integer result, which can then
	 * be assigned to a BigInteger variable or used in an expression.
	 * Example:
	 *     BigInteger a(1), b = 1;
	 *     BigInteger c = a + b;
	 *
	 * (2) Overloaded assignment operators:
	 *     +=, -=, *=, /=, %=, flipSign, &=, |=, ^=, <<=, >>=, ++, --.
	 * Again, these are used on big integers just like on ints.  They take
	 * one writable big integer that both provides an operand and receives a
	 * result.  Most also take a second read-only operand.
	 * Example:
	 *     BigInteger a(1), b(1);
	 *     a += b;
	 *
	 * (3) Copy-less operations: `add', `subtract', etc.
	 * These named methods take operands as arguments and store the result
	 * in the receiver (*this), avoiding unnecessary copies and allocations.
	 * `divideWithRemainder' is special: it both takes the dividend from and
	 * stores the remainder into the receiver, and it takes a separate
	 * object in which to store the quotient.  NOTE: If you are wondering
	 * why these don't return a value, you probably mean to use the
	 * overloaded return-by-value operators instead.
	 *
	 * Examples:
	 *     BigInteger a(43), b(7), c, d;
	 *
	 *     c = a + b;   // Now c == 50.
	 *     c.add(a, b); // Same effect but without the two copies.
	 *
	 *     c.divideWithRemainder(b, d);
	 *     // 50 / 7; now d == 7 (quotient) and c == 1 (remainder).
	 *
	 *     // ``Aliased'' calls now do the right thing using a temporary
	 *     // copy, but see note on `divideWithRemainder'.
	 *     a.add(a, b);
	 */

	// COPY-LESS OPERATIONS

	// These 8: Arguments are read-only operands, result is saved in *this.
	void add(const BigUnsigned &a, const BigUnsigned &b);
	void subtract(const BigUnsigned &a, const BigUnsigned &b);
	void multiply(const BigUnsigned &a, const BigUnsigned &b);
	void bitAnd(const BigUnsigned &a, const BigUnsigned &b);
	void bitOr(const BigUnsigned &a, const BigUnsigned &b);
	void bitXor(const BigUnsigned &a, const BigUnsigned &b);
	/* Negative shift amounts translate to opposite-direction shifts,
	 * except for -2^(8*sizeof(int)-1) which is unimplemented. */
	void bitShiftLeft(const BigUnsigned &a, int b);
	void bitShiftRight(const BigUnsigned &a, int b);

	/* `a.divideWithRemainder(b, q)' is like `q = a / b, a %= b'.
	 * / and % use semantics similar to Knuth's, which differ from the
	 * primitive integer semantics under division by zero.  See the
	 * implementation in BigUnsigned.cc for details.
	 * `a.divideWithRemainder(b, a)' throws an exception: it doesn't make
	 * sense to write quotient and remainder into the same variable. */
	void divideWithRemainder(const BigUnsigned &b, BigUnsigned &q);

	/* `divide' and `modulo' are no longer offered.  Use
	 * `divideWithRemainder' instead. */

	// OVERLOADED RETURN-BY-VALUE OPERATORS
	BigUnsigned operator +(const BigUnsigned &x) const;
	BigUnsigned operator -(const BigUnsigned &x) const;
	BigUnsigned operator *(const BigUnsigned &x) const;
	BigUnsigned operator /(const BigUnsigned &x) const;
	BigUnsigned operator %(const BigUnsigned &x) const;
	/* OK, maybe unary minus could succeed in one case, but it really
	 * shouldn't be used, so it isn't provided. */
	BigUnsigned operator &(const BigUnsigned &x) const;
	BigUnsigned operator |(const BigUnsigned &x) const;
	BigUnsigned operator ^(const BigUnsigned &x) const;
	BigUnsigned operator <<(int b) const;
	BigUnsigned operator >>(int b) const;

	// OVERLOADED ASSIGNMENT OPERATORS
	void operator +=(const BigUnsigned &x);
	void operator -=(const BigUnsigned &x);
	void operator *=(const BigUnsigned &x);
	void operator /=(const BigUnsigned &x);
	void operator %=(const BigUnsigned &x);
	void operator &=(const BigUnsigned &x);
	void operator |=(const BigUnsigned &x);
	void operator ^=(const BigUnsigned &x);
	void operator <<=(int b);
	void operator >>=(int b);

	/* INCREMENT/DECREMENT OPERATORS
	 * To discourage messy coding, these do not return *this, so prefix
	 * and postfix behave the same. */
	void operator ++(   );
	void operator ++(int);
	void operator --(   );
	void operator --(int);

	// Helper function that needs access to BigUnsigned internals
	friend Blk getShiftedBlock(const BigUnsigned &num, Index x,
			unsigned int y);

	// See BigInteger.cc.
	template <class X>
	friend X convertBigUnsignedToPrimitiveAccess(const BigUnsigned &a);
};

/* Implementing the return-by-value and assignment operators in terms of the
 * copy-less operations.  The copy-less operations are responsible for making
 * any necessary temporary copies to work around aliasing. */

inline BigUnsigned BigUnsigned::operator +(const BigUnsigned &x) const {
	BigUnsigned ans;
	ans.add(*this, x);
	return ans;
}
inline BigUnsigned BigUnsigned::operator -(const BigUnsigned &x) const {
	BigUnsigned ans;
	ans.subtract(*this, x);
	return ans;
}
inline BigUnsigned BigUnsigned::operator *(const BigUnsigned &x) const {
	BigUnsigned ans;
	ans.multiply(*this, x);
	return ans;
}
inline BigUnsigned BigUnsigned::operator /(const BigUnsigned &x) const {
	if (x.isZero()) throw "BigUnsigned::operator /: division by zero";
	BigUnsigned q, r;
	r = *this;
	r.divideWithRemainder(x, q);
	return q;
}
inline BigUnsigned BigUnsigned::operator %(const BigUnsigned &x) const {
	if (x.isZero()) throw "BigUnsigned::operator %: division by zero";
	BigUnsigned q, r;
	r = *this;
	r.divideWithRemainder(x, q);
	return r;
}
inline BigUnsigned BigUnsigned::operator &(const BigUnsigned &x) const {
	BigUnsigned ans;
	ans.bitAnd(*this, x);
	return ans;
}
inline BigUnsigned BigUnsigned::operator |(const BigUnsigned &x) const {
	BigUnsigned ans;
	ans.bitOr(*this, x);
	return ans;
}
inline BigUnsigned BigUnsigned::operator ^(const BigUnsigned &x) const {
	BigUnsigned ans;
	ans.bitXor(*this, x);
	return ans;
}
inline BigUnsigned BigUnsigned::operator <<(int b) const {
	BigUnsigned ans;
	ans.bitShiftLeft(*this, b);
	return ans;
}
inline BigUnsigned BigUnsigned::operator >>(int b) const {
	BigUnsigned ans;
	ans.bitShiftRight(*this, b);
	return ans;
}

inline void BigUnsigned::operator +=(const BigUnsigned &x) {
	add(*this, x);
}
inline void BigUnsigned::operator -=(const BigUnsigned &x) {
	subtract(*this, x);
}
inline void BigUnsigned::operator *=(const BigUnsigned &x) {
	multiply(*this, x);
}
inline void BigUnsigned::operator /=(const BigUnsigned &x) {
	if (x.isZero()) throw "BigUnsigned::operator /=: division by zero";
	/* The following technique is slightly faster than copying *this first
	 * when x is large. */
	BigUnsigned q;
	divideWithRemainder(x, q);
	// *this contains the remainder, but we overwrite it with the quotient.
	*this = q;
}
inline void BigUnsigned::operator %=(const BigUnsigned &x) {
	if (x.isZero()) throw "BigUnsigned::operator %=: division by zero";
	BigUnsigned q;
	// Mods *this by x.  Don't care about quotient left in q.
	divideWithRemainder(x, q);
}
inline void BigUnsigned::operator &=(const BigUnsigned &x) {
	bitAnd(*this, x);
}
inline void BigUnsigned::operator |=(const BigUnsigned &x) {
	bitOr(*this, x);
}
inline void BigUnsigned::operator ^=(const BigUnsigned &x) {
	bitXor(*this, x);
}
inline void BigUnsigned::operator <<=(int b) {
	bitShiftLeft(*this, b);
}
inline void BigUnsigned::operator >>=(int b) {
	bitShiftRight(*this, b);
}

/* Templates for conversions of BigUnsigned to and from primitive integers.
 * BigInteger.cc needs to instantiate convertToPrimitive, and the uses in
 * BigUnsigned.cc didn't do the trick; I think g++ inlined convertToPrimitive
 * instead of generating linkable instantiations.  So for consistency, I put
 * all the templates here. */

// CONSTRUCTION FROM PRIMITIVE INTEGERS

/* Initialize this BigUnsigned from the given primitive integer.  The same
 * pattern works for all primitive integer types, so I put it into a template to
 * reduce code duplication.  (Don't worry: this is protected and we instantiate
 * it only with primitive integer types.)  Type X could be signed, but x is
 * known to be nonnegative. */
template <class X>
void BigUnsigned::initFromPrimitive(X x) {
	if (x == 0)
		; // NumberlikeArray already initialized us to zero.
	else {
		// Create a single block.  blk is NULL; no need to delete it.
		cap = 1;
		blk = new Blk[1];
		len = 1;
		blk[0] = Blk(x);
	}
}

/* Ditto, but first check that x is nonnegative.  I could have put the check in
 * initFromPrimitive and let the compiler optimize it out for unsigned-type
 * instantiations, but I wanted to avoid the warning stupidly issued by g++ for
 * a condition that is constant in *any* instantiation, even if not in all. */
template <class X>
void BigUnsigned::initFromSignedPrimitive(X x) {
	if (x < 0)
		throw "BigUnsigned constructor: "
			"Cannot construct a BigUnsigned from a negative number";
	else
		initFromPrimitive(x);
}

// CONVERSION TO PRIMITIVE INTEGERS

/* Template with the same idea as initFromPrimitive.  This might be slightly
 * slower than the previous version with the masks, but it's much shorter and
 * clearer, which is the library's stated goal. */
template <class X>
X BigUnsigned::convertToPrimitive() const {
	if (len == 0)
		// The number is zero; return zero.
		return 0;
	else if (len == 1) {
		// The single block might fit in an X.  Try the conversion.
		X x = X(blk[0]);
		// Make sure the result accurately represents the block.
		if (Blk(x) == blk[0])
			// Successful conversion.
			return x;
		// Otherwise fall through.
	}
	throw "BigUnsigned::to<Primitive>: "
		"Value is too big to fit in the requested type";
}

/* Wrap the above in an x >= 0 test to make sure we got a nonnegative result,
 * not a negative one that happened to convert back into the correct nonnegative
 * one.  (E.g., catch incorrect conversion of 2^31 to the long -2^31.)  Again,
 * separated to avoid a g++ warning. */
template <class X>
X BigUnsigned::convertToSignedPrimitive() const {
	X x = convertToPrimitive<X>();
	if (x >= 0)
		return x;
	else
		throw "BigUnsigned::to(Primitive): "
			"Value is too big to fit in the requested type";
}

#endif

// file: /bigint/BigUnsignedInABase.hh

#ifndef BIGUNSIGNEDINABASE_H
#define BIGUNSIGNEDINABASE_H

// #include "NumberlikeArray.hh"
// #include "BigUnsigned.hh"
// #include <string>

/*
 * A BigUnsignedInABase object represents a nonnegative integer of size limited
 * only by available memory, represented in a user-specified base that can fit
 * in an `unsigned short' (most can, and this saves memory).
 *
 * BigUnsignedInABase is intended as an intermediary class with little
 * functionality of its own.  BigUnsignedInABase objects can be constructed
 * from, and converted to, BigUnsigneds (requiring multiplication, mods, etc.)
 * and `std::string's (by switching digit values for appropriate characters).
 *
 * BigUnsignedInABase is similar to BigUnsigned.  Note the following:
 *
 * (1) They represent the number in exactly the same way, except that
 * BigUnsignedInABase uses ``digits'' (or Digit) where BigUnsigned uses
 * ``blocks'' (or Blk).
 *
 * (2) Both use the management features of NumberlikeArray.  (In fact, my desire
 * to add a BigUnsignedInABase class without duplicating a lot of code led me to
 * introduce NumberlikeArray.)
 *
 * (3) The only arithmetic operation supported by BigUnsignedInABase is an
 * equality test.  Use BigUnsigned for arithmetic.
 */

class BigUnsignedInABase : protected NumberlikeArray<unsigned short> {

public:
	// The digits of a BigUnsignedInABase are unsigned shorts.
	typedef unsigned short Digit;
	// That's also the type of a base.
	typedef Digit Base;

protected:
	// The base in which this BigUnsignedInABase is expressed
	Base base;

	// Creates a BigUnsignedInABase with a capacity; for internal use.
	BigUnsignedInABase(int, Index c) : NumberlikeArray<Digit>(0, c) {}

	// Decreases len to eliminate any leading zero digits.
	void zapLeadingZeros() {
		while (len > 0 && blk[len - 1] == 0)
			len--;
	}

public:
	// Constructs zero in base 2.
	BigUnsignedInABase() : NumberlikeArray<Digit>(), base(2) {}

	// Copy constructor
	BigUnsignedInABase(const BigUnsignedInABase &x) : NumberlikeArray<Digit>(x), base(x.base) {}

	// Assignment operator
	void operator =(const BigUnsignedInABase &x) {
		NumberlikeArray<Digit>::operator =(x);
		base = x.base;
	}

	// Constructor that copies from a given array of digits.
	BigUnsignedInABase(const Digit *d, Index l, Base base);

	// Destructor.  NumberlikeArray does the delete for us.
	~BigUnsignedInABase() {}

	// LINKS TO BIGUNSIGNED
	BigUnsignedInABase(const BigUnsigned &x, Base base);
	operator BigUnsigned() const;

	/* LINKS TO STRINGS
	 *
	 * These use the symbols ``0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'' to
	 * represent digits of 0 through 35.  When parsing strings, lowercase is
	 * also accepted.
	 *
	 * All string representations are big-endian (big-place-value digits
	 * first).  (Computer scientists have adopted zero-based counting; why
	 * can't they tolerate little-endian numbers?)
	 *
	 * No string representation has a ``base indicator'' like ``0x''.
	 *
	 * An exception is made for zero: it is converted to ``0'' and not the
	 * empty string.
	 *
	 * If you want different conventions, write your own routines to go
	 * between BigUnsignedInABase and strings.  It's not hard.
	 */
	operator std::string() const;
	BigUnsignedInABase(const std::string &s, Base base);

public:

	// ACCESSORS
	Base getBase() const { return base; }

	// Expose these from NumberlikeArray directly.
	using NumberlikeArray<Digit>::getCapacity;
	using NumberlikeArray<Digit>::getLength;

	/* Returns the requested digit, or 0 if it is beyond the length (as if
	 * the number had 0s infinitely to the left). */
	Digit getDigit(Index i) const { return i >= len ? 0 : blk[i]; }

	// The number is zero if and only if the canonical length is zero.
	bool isZero() const { return NumberlikeArray<Digit>::isEmpty(); }

	/* Equality test.  For the purposes of this test, two BigUnsignedInABase
	 * values must have the same base to be equal. */
	bool operator ==(const BigUnsignedInABase &x) const {
		return base == x.base && NumberlikeArray<Digit>::operator ==(x);
	}
	bool operator !=(const BigUnsignedInABase &x) const { return !operator ==(x); }

};

#endif

// file: /bigint/BigInteger.hh

#ifndef BIGINTEGER_H
#define BIGINTEGER_H

// #include "BigUnsigned.hh"

/* A BigInteger object represents a signed integer of size limited only by
 * available memory.  BigUnsigneds support most mathematical operators and can
 * be converted to and from most primitive integer types.
 *
 * A BigInteger is just an aggregate of a BigUnsigned and a sign.  (It is no
 * longer derived from BigUnsigned because that led to harmful implicit
 * conversions.) */
class BigInteger {

public:
	typedef BigUnsigned::Blk Blk;
	typedef BigUnsigned::Index Index;
	typedef BigUnsigned::CmpRes CmpRes;
	static const CmpRes
		less    = BigUnsigned::less   ,
		equal   = BigUnsigned::equal  ,
		greater = BigUnsigned::greater;
	// Enumeration for the sign of a BigInteger.
	enum Sign { negative = -1, zero = 0, positive = 1 };

protected:
	Sign sign;
	BigUnsigned mag;

public:
	// Constructs zero.
	BigInteger() : sign(zero), mag() {}

	// Copy constructor
	BigInteger(const BigInteger &x) : sign(x.sign), mag(x.mag) {};

	// Assignment operator
	void operator=(const BigInteger &x);

	// Constructor that copies from a given array of blocks with a sign.
	BigInteger(const Blk *b, Index blen, Sign s);

	// Nonnegative constructor that copies from a given array of blocks.
	BigInteger(const Blk *b, Index blen) : mag(b, blen) {
		sign = mag.isZero() ? zero : positive;
	}

	// Constructor from a BigUnsigned and a sign
	BigInteger(const BigUnsigned &x, Sign s);

	// Nonnegative constructor from a BigUnsigned
	BigInteger(const BigUnsigned &x) : mag(x) {
		sign = mag.isZero() ? zero : positive;
	}

	// Constructors from primitive integer types
	BigInteger(unsigned long  x);
	BigInteger(         long  x);
	BigInteger(unsigned int   x);
	BigInteger(         int   x);
	BigInteger(unsigned short x);
	BigInteger(         short x);

	/* Converters to primitive integer types
	 * The implicit conversion operators caused trouble, so these are now
	 * named. */
	unsigned long  toUnsignedLong () const;
	long           toLong         () const;
	unsigned int   toUnsignedInt  () const;
	int            toInt          () const;
	unsigned short toUnsignedShort() const;
	short          toShort        () const;
protected:
	// Helper
	template <class X> X convertToUnsignedPrimitive() const;
	template <class X, class UX> X convertToSignedPrimitive() const;
public:

	// ACCESSORS
	Sign getSign() const { return sign; }
	/* The client can't do any harm by holding a read-only reference to the
	 * magnitude. */
	const BigUnsigned &getMagnitude() const { return mag; }

	// Some accessors that go through to the magnitude
	Index getLength() const { return mag.getLength(); }
	Index getCapacity() const { return mag.getCapacity(); }
	Blk getBlock(Index i) const { return mag.getBlock(i); }
	bool isZero() const { return sign == zero; } // A bit special

	// COMPARISONS

	// Compares this to x like Perl's <=>
	CmpRes compareTo(const BigInteger &x) const;

	// Ordinary comparison operators
	bool operator ==(const BigInteger &x) const {
		return sign == x.sign && mag == x.mag;
	}
	bool operator !=(const BigInteger &x) const { return !operator ==(x); };
	bool operator < (const BigInteger &x) const { return compareTo(x) == less   ; }
	bool operator <=(const BigInteger &x) const { return compareTo(x) != greater; }
	bool operator >=(const BigInteger &x) const { return compareTo(x) != less   ; }
	bool operator > (const BigInteger &x) const { return compareTo(x) == greater; }

	// OPERATORS -- See the discussion in BigUnsigned.hh.
	void add     (const BigInteger &a, const BigInteger &b);
	void subtract(const BigInteger &a, const BigInteger &b);
	void multiply(const BigInteger &a, const BigInteger &b);
	/* See the comment on BigUnsigned::divideWithRemainder.  Semantics
	 * differ from those of primitive integers when negatives and/or zeros
	 * are involved. */
	void divideWithRemainder(const BigInteger &b, BigInteger &q);
	void negate(const BigInteger &a);

	/* Bitwise operators are not provided for BigIntegers.  Use
	 * getMagnitude to get the magnitude and operate on that instead. */

	BigInteger operator +(const BigInteger &x) const;
	BigInteger operator -(const BigInteger &x) const;
	BigInteger operator *(const BigInteger &x) const;
	BigInteger operator /(const BigInteger &x) const;
	BigInteger operator %(const BigInteger &x) const;
	BigInteger operator -() const;

	void operator +=(const BigInteger &x);
	void operator -=(const BigInteger &x);
	void operator *=(const BigInteger &x);
	void operator /=(const BigInteger &x);
	void operator %=(const BigInteger &x);
	void flipSign();

	// INCREMENT/DECREMENT OPERATORS
	void operator ++(   );
	void operator ++(int);
	void operator --(   );
	void operator --(int);
};

// NORMAL OPERATORS
/* These create an object to hold the result and invoke
 * the appropriate put-here operation on it, passing
 * this and x.  The new object is then returned. */
inline BigInteger BigInteger::operator +(const BigInteger &x) const {
	BigInteger ans;
	ans.add(*this, x);
	return ans;
}
inline BigInteger BigInteger::operator -(const BigInteger &x) const {
	BigInteger ans;
	ans.subtract(*this, x);
	return ans;
}
inline BigInteger BigInteger::operator *(const BigInteger &x) const {
	BigInteger ans;
	ans.multiply(*this, x);
	return ans;
}
inline BigInteger BigInteger::operator /(const BigInteger &x) const {
	if (x.isZero()) throw "BigInteger::operator /: division by zero";
	BigInteger q, r;
	r = *this;
	r.divideWithRemainder(x, q);
	return q;
}
inline BigInteger BigInteger::operator %(const BigInteger &x) const {
	if (x.isZero()) throw "BigInteger::operator %: division by zero";
	BigInteger q, r;
	r = *this;
	r.divideWithRemainder(x, q);
	return r;
}
inline BigInteger BigInteger::operator -() const {
	BigInteger ans;
	ans.negate(*this);
	return ans;
}

/*
 * ASSIGNMENT OPERATORS
 *
 * Now the responsibility for making a temporary copy if necessary
 * belongs to the put-here operations.  See Assignment Operators in
 * BigUnsigned.hh.
 */
inline void BigInteger::operator +=(const BigInteger &x) {
	add(*this, x);
}
inline void BigInteger::operator -=(const BigInteger &x) {
	subtract(*this, x);
}
inline void BigInteger::operator *=(const BigInteger &x) {
	multiply(*this, x);
}
inline void BigInteger::operator /=(const BigInteger &x) {
	if (x.isZero()) throw "BigInteger::operator /=: division by zero";
	/* The following technique is slightly faster than copying *this first
	 * when x is large. */
	BigInteger q;
	divideWithRemainder(x, q);
	// *this contains the remainder, but we overwrite it with the quotient.
	*this = q;
}
inline void BigInteger::operator %=(const BigInteger &x) {
	if (x.isZero()) throw "BigInteger::operator %=: division by zero";
	BigInteger q;
	// Mods *this by x.  Don't care about quotient left in q.
	divideWithRemainder(x, q);
}
// This one is trivial
inline void BigInteger::flipSign() {
	sign = Sign(-sign);
}

#endif

// file: /bigint/BigIntegerAlgorithms.hh

#ifndef BIGINTEGERALGORITHMS_H
#define BIGINTEGERALGORITHMS_H

// #include "BigInteger.hh"

/* Some mathematical algorithms for big integers.
 * This code is new and, as such, experimental. */

// Returns the greatest common divisor of a and b.
BigUnsigned gcd(BigUnsigned a, BigUnsigned b);

/* Extended Euclidean algorithm.
 * Given m and n, finds gcd g and numbers r, s such that r*m + s*n == g. */
void extendedEuclidean(BigInteger m, BigInteger n,
		BigInteger &g, BigInteger &r, BigInteger &s);

/* Returns the multiplicative inverse of x modulo n, or throws an exception if
 * they have a common factor. */
BigUnsigned modinv(const BigInteger &x, const BigUnsigned &n);

// Returns (base ^ exponent) % modulus.
BigUnsigned modexp(const BigInteger &base, const BigUnsigned &exponent,
		const BigUnsigned &modulus);

#endif

// file: /bigint/BigIntegerLibrary.hh

// This header file includes all of the library header files.

// #include "NumberlikeArray.hh"
// #include "BigUnsigned.hh"
// #include "BigInteger.hh"
// #include "BigIntegerAlgorithms.hh"
// #include "BigUnsignedInABase.hh"
// #include "BigIntegerUtils.hh"

// file: /bigint/BigIntegerUtils.hh

#ifndef BIGINTEGERUTILS_H
#define BIGINTEGERUTILS_H

// #include "BigInteger.hh"
// #include <string>
// #include <iostream>

/* This file provides:
 * - Convenient std::string <-> BigUnsigned/BigInteger conversion routines
 * - std::ostream << operators for BigUnsigned/BigInteger */

// std::string conversion routines.  Base 10 only.
std::string bigUnsignedToString(const BigUnsigned &x);
std::string bigIntegerToString(const BigInteger &x);
BigUnsigned stringToBigUnsigned(const std::string &s);
BigInteger stringToBigInteger(const std::string &s);

// Creates a BigInteger from data such as `char's; read below for details.
template <class T>
BigInteger dataToBigInteger(const T* data, BigInteger::Index length, BigInteger::Sign sign);

// Outputs x to os, obeying the flags `dec', `hex', `bin', and `showbase'.
std::ostream &operator <<(std::ostream &os, const BigUnsigned &x);

// Outputs x to os, obeying the flags `dec', `hex', `bin', and `showbase'.
// My somewhat arbitrary policy: a negative sign comes before a base indicator (like -0xFF).
std::ostream &operator <<(std::ostream &os, const BigInteger &x);

// BEGIN TEMPLATE DEFINITIONS.

/*
 * Converts binary data to a BigInteger.
 * Pass an array `data', its length, and the desired sign.
 *
 * Elements of `data' may be of any type `T' that has the following
 * two properties (this includes almost all integral types):
 *
 * (1) `sizeof(T)' correctly gives the amount of binary data in one
 * value of `T' and is a factor of `sizeof(Blk)'.
 *
 * (2) When a value of `T' is casted to a `Blk', the low bytes of
 * the result contain the desired binary data.
 */
template <class T>
BigInteger dataToBigInteger(const T* data, BigInteger::Index length, BigInteger::Sign sign) {
	// really ceiling(numBytes / sizeof(BigInteger::Blk))
	unsigned int pieceSizeInBits = 8 * sizeof(T);
	unsigned int piecesPerBlock = sizeof(BigInteger::Blk) / sizeof(T);
	unsigned int numBlocks = (length + piecesPerBlock - 1) / piecesPerBlock;

	// Allocate our block array
	BigInteger::Blk *blocks = new BigInteger::Blk[numBlocks];

	BigInteger::Index blockNum, pieceNum, pieceNumHere;

	// Convert
	for (blockNum = 0, pieceNum = 0; blockNum < numBlocks; blockNum++) {
		BigInteger::Blk curBlock = 0;
		for (pieceNumHere = 0; pieceNumHere < piecesPerBlock && pieceNum < length;
			pieceNumHere++, pieceNum++)
			curBlock |= (BigInteger::Blk(data[pieceNum]) << (pieceSizeInBits * pieceNumHere));
		blocks[blockNum] = curBlock;
	}

	// Create the BigInteger.
	BigInteger x(blocks, numBlocks, sign);

	delete [] blocks;
	return x;
}

#endif

// file: zxing/zxing.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Copyright 2013 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#ifndef __ZXING_H_
#define __ZXING_H_

#define ZXING_ARRAY_LEN(v) ((int)(sizeof(v)/sizeof(v[0])))
#define ZX_LOG_DIGITS(digits) \
    ((digits == 8) ? 3 : \
     ((digits == 16) ? 4 : \
      ((digits == 32) ? 5 : \
       ((digits == 64) ? 6 : \
        ((digits == 128) ? 7 : \
         (-1))))))

#ifndef ZXING_DEBUG
#define ZXING_DEBUG 0
#endif

namespace zxing {
typedef char byte;
typedef bool boolean;
}

#include <limits>

#if defined(_WIN32) || defined(_WIN64)

#include <float.h>

namespace zxing {
inline bool isnan(float v) {return _isnan(v) != 0;}
inline bool isnan(double v) {return _isnan(v) != 0;}
inline float nan() {return std::numeric_limits<float>::quiet_NaN();}
}

#else

#include <cmath>

namespace zxing {
inline bool isnan(float v) {return std::isnan(v);}
inline bool isnan(double v) {return std::isnan(v);}
inline float nan() {return std::numeric_limits<float>::quiet_NaN();}
}

#endif

#if ZXING_DEBUG

#include <iostream>
#include <string>

using std::cout;
using std::cerr;
using std::endl;
using std::flush;
using std::string;
using std::ostream;

#if ZXING_DEBUG_TIMER

#include <sys/time.h>

namespace zxing {

class DebugTimer {
public:
  DebugTimer(char const* string_) : chars(string_) {
    gettimeofday(&start, 0);
  }

  DebugTimer(std::string const& string_) : chars(0), string(string_) {
    gettimeofday(&start, 0);
  }

  void mark(char const* string) {
    struct timeval end;
    gettimeofday(&end, 0);
    int diff =
      (end.tv_sec - start.tv_sec)*1000*1000+(end.tv_usec - start.tv_usec);

    cerr << diff << " " << string << '\n';
  }

  void mark(std::string string) {
    mark(string.c_str());
  }

  ~DebugTimer() {
    if (chars) {
      mark(chars);
    } else {
      mark(string.c_str());
    }
  }

private:
  char const* const chars;
  std::string string;
  struct timeval start;
};

}

#define ZXING_TIME(string) DebugTimer __timer__ (string)
#define ZXING_TIME_MARK(string) __timer__.mark(string)

#endif

#endif // ZXING_DEBUG

#ifndef ZXING_TIME
#define ZXING_TIME(string) (void)0
#endif
#ifndef ZXING_TIME_MARK
#define ZXING_TIME_MARK(string) (void)0
#endif

#endif


// file: zxing/Exception.h

#ifndef __EXCEPTION_H__
// #define __EXCEPTION_H__

/*
 *  Exception.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <string>
// #include <exception>

namespace zxing {

class Exception : public std::exception {
private:
  char const* const message;

public:
  Exception() throw() : message(0) {}
  Exception(const char* msg) throw() : message(copy(msg)) {}
  Exception(Exception const& that) throw() : std::exception(that), message(copy(that.message)) {}
  ~Exception() throw() {
    if(message) {
      deleteMessage();
    }
  }
  char const* what() const throw() {return message ? message : "";}

private:
  static char const* copy(char const*);
  void deleteMessage();
};

}

#endif // __EXCEPTION_H__

// file: zxing/common/IllegalArgumentException.h

#ifndef __ILLEGAL_ARGUMENT_EXCEPTION_H__
// #define __ILLEGAL_ARGUMENT_EXCEPTION_H__

/*
 *  IllegalArgumentException.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Exception.h>

namespace zxing {

class IllegalArgumentException : public Exception {
public:
  IllegalArgumentException();
  IllegalArgumentException(const char *msg);
  ~IllegalArgumentException() throw();
};

}

#endif // __ILLEGAL_ARGUMENT_EXCEPTION_H__

// file: zxing/common/Counted.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __COUNTED_H__
// #define __COUNTED_H__

/*
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <iostream>

namespace zxing {

/* base class for reference-counted objects */
class Counted {
private:
  unsigned int count_;
public:
  Counted() :
      count_(0) {
  }
  virtual ~Counted() {
  }
  Counted *retain() {
    count_++;
    return this;
  }
  void release() {
    count_--;
    if (count_ == 0) {
      count_ = 0xDEADF001;
      delete this;
    }
  }


  /* return the current count for denugging purposes or similar */
  int count() const {
    return count_;
  }
};

/* counting reference to reference-counted objects */
template<typename T> class Ref {
private:
public:
  T *object_;
  explicit Ref(T *o = 0) :
      object_(0) {
    reset(o);
  }
  Ref(const Ref &other) :
      object_(0) {
    reset(other.object_);
  }

  template<class Y>
  Ref(const Ref<Y> &other) :
      object_(0) {
    reset(other.object_);
  }

  ~Ref() {
    if (object_) {
      object_->release();
    }
  }

  void reset(T *o) {
    if (o) {
      o->retain();
    }
    if (object_ != 0) {
      object_->release();
    }
    object_ = o;
  }
  Ref& operator=(const Ref &other) {
    reset(other.object_);
    return *this;
  }
  template<class Y>
  Ref& operator=(const Ref<Y> &other) {
    reset(other.object_);
    return *this;
  }
  Ref& operator=(T* o) {
    reset(o);
    return *this;
  }
  template<class Y>
  Ref& operator=(Y* o) {
    reset(o);
    return *this;
  }

  T& operator*() {
    return *object_;
  }
  T* operator->() const {
    return object_;
  }
  operator T*() const {
    return object_;
  }

  bool operator==(const T* that) {
    return object_ == that;
  }
  bool operator==(const Ref &other) const {
    return object_ == other.object_ || *object_ == *(other.object_);
  }
  template<class Y>
  bool operator==(const Ref<Y> &other) const {
    return object_ == other.object_ || *object_ == *(other.object_);
  }

  bool operator!=(const T* that) {
    return !(*this == that);
  }

  bool empty() const {
    return object_ == 0;
  }
};

}

#endif // __COUNTED_H__

// file: zxing/common/Array.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __ARRAY_H__
// #define __ARRAY_H__

/*
 *  Array.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <vector>

// #include <zxing/common/Counted.h>

namespace zxing {

    template<typename T> class Array : public Counted {
    protected:
    public:
        std::vector<T> values_;
        Array() {}
        Array(int n) :
        Counted(), values_(n, T()) {
        }
        Array(T const* ts, int n) :
        Counted(), values_(ts, ts+n) {
        }
        Array(T const* ts, T const* te) :
        Counted(), values_(ts, te) {
        }
        Array(T v, int n) :
        Counted(), values_(n, v) {
        }
        Array(std::vector<T> &v) :
        Counted(), values_(v) {
        }
        Array(Array<T> &other) :
        Counted(), values_(other.values_) {
        }
        Array(Array<T> *other) :
        Counted(), values_(other->values_) {
        }
        virtual ~Array() {
        }
        Array<T>& operator=(const Array<T> &other) {
            values_ = other.values_;
            return *this;
        }
        Array<T>& operator=(const std::vector<T> &array) {
            values_ = array;
            return *this;
        }
        T const& operator[](int i) const {
            return values_[i];
        }
        T& operator[](int i) {
            return values_[i];
        }
        size_t size() const {
            return values_.size();
        }
        bool empty() const {
            return values_.size() == 0;
        }
        std::vector<T> const& values() const {
            return values_;
        }
        std::vector<T>& values() {
            return values_;
        }
    };

    template<typename T> class ArrayRef : public Counted {
    private:
    public:
        Array<T> *array_;
        ArrayRef() :
        array_(0) {
        }
        explicit ArrayRef(int n) :
        array_(0) {
            reset(new Array<T> (n));
        }
        ArrayRef(T *ts, int n) :
        array_(0) {
            reset(new Array<T> (ts, n));
        }
        ArrayRef(Array<T> *a) :
        array_(0) {
            reset(a);
        }
        ArrayRef(const ArrayRef &other) :
        Counted(), array_(0) {
            reset(other.array_);
        }

        template<class Y>
        ArrayRef(const ArrayRef<Y> &other) :
        array_(0) {
            reset(static_cast<const Array<T> *>(other.array_));
        }

        ~ArrayRef() {
            if (array_) {
                array_->release();
            }
            array_ = 0;
        }

        T const& operator[](int i) const {
            return (*array_)[i];
        }

        T& operator[](int i) {
            return (*array_)[i];
        }

        void reset(Array<T> *a) {
            if (a) {
                a->retain();
            }
            if (array_) {
                array_->release();
            }
            array_ = a;
        }
        void reset(const ArrayRef<T> &other) {
            reset(other.array_);
        }
        ArrayRef<T>& operator=(const ArrayRef<T> &other) {
            reset(other);
            return *this;
        }
        ArrayRef<T>& operator=(Array<T> *a) {
            reset(a);
            return *this;
        }

        Array<T>& operator*() const {
            return *array_;
        }

        Array<T>* operator->() const {
            return array_;
        }

        operator bool () const {
            return array_ != 0;
        }
        bool operator ! () const {
            return array_ == 0;
        }
    };

} // namespace zxing

#endif // __ARRAY_H__

// file: zxing/common/BitArray.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __BIT_ARRAY_H__
// #define __BIT_ARRAY_H__

/*
 *  Copyright 2010 ZXing authors. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ZXing.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/IllegalArgumentException.h>
// #include <zxing/common/Array.h>
// #include <vector>
// #include <limits>
// #include <iostream>

namespace zxing {

class BitArray : public Counted {
public:
  static const int bitsPerWord = std::numeric_limits<unsigned int>::digits;

private:
  int size;
  ArrayRef<int> bits;
  static const int logBits = ZX_LOG_DIGITS(bitsPerWord);
  static const int bitsMask = (1 << logBits) - 1;

public:
  BitArray(int size);
  ~BitArray();
  int getSize() const;

  bool get(int i) const {
    return (bits[i >> logBits] & (1 << (i & bitsMask))) != 0;
  }

  void set(int i) {
    bits[i >> logBits] |= 1 << (i & bitsMask);
  }

  int getNextSet(int from);
  int getNextUnset(int from);

  void setBulk(int i, int newBits);
  void setRange(int start, int end);
  void clear();
  bool isRange(int start, int end, bool value);
  std::vector<int>& getBitArray();

  void reverse();

  class Reverse {
   private:
    Ref<BitArray> array;
   public:
    Reverse(Ref<BitArray> array);
    ~Reverse();
  };

private:
  static int makeArraySize(int size);
};

std::ostream& operator << (std::ostream&, BitArray const&);

}

#endif // __BIT_ARRAY_H__

// file: zxing/common/BitMatrix.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __BIT_MATRIX_H__
// #define __BIT_MATRIX_H__

/*
 *  BitMatrix.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/common/Array.h>
// #include <limits>

namespace zxing {

class BitMatrix : public Counted {
public:
  static const int bitsPerWord = std::numeric_limits<unsigned int>::digits;

private:
  int width;
  int height;
  int rowSize;
  ArrayRef<int> bits;

#define ZX_LOG_DIGITS(digits) \
    ((digits == 8) ? 3 : \
     ((digits == 16) ? 4 : \
      ((digits == 32) ? 5 : \
       ((digits == 64) ? 6 : \
        ((digits == 128) ? 7 : \
         (-1))))))

  static const int logBits = ZX_LOG_DIGITS(bitsPerWord);
  static const int bitsMask = (1 << logBits) - 1;

public:
  BitMatrix(int dimension);
  BitMatrix(int width, int height);

  ~BitMatrix();

  bool get(size_t x, size_t y) const {
    int offset = (int)(y * rowSize + (x >> logBits));
    return ((((unsigned)bits[offset]) >> (x & bitsMask)) & 1) != 0;
  }

  void set(size_t x, size_t y) {
    int offset = (int)(y * rowSize + (x >> logBits));
    bits[offset] |= 1 << (x & bitsMask);
  }

  void flip(size_t x, size_t y);
  void clear();
  void setRegion(int left, int top, int width, int height);
  Ref<BitArray> getRow(int y, Ref<BitArray> row);

  int getWidth() const;
  int getHeight() const;

  ArrayRef<int> getTopLeftOnBit() const;
  ArrayRef<int> getBottomRightOnBit() const;

  friend std::ostream& operator<<(std::ostream &out, const BitMatrix &bm);
  const char *description();

private:
  inline void init(int, int);

  BitMatrix(const BitMatrix&);
  BitMatrix& operator =(const BitMatrix&);
};

}

#endif // __BIT_MATRIX_H__

// file: zxing/common/Str.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __STR_H__
// #define __STR_H__

/*
 *  Str.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <string>
// #include <iostream>
// #include <zxing/common/Counted.h>

namespace zxing {

class String;
std::ostream& operator << (std::ostream& out, String const& s);

class String : public Counted {
private:
  std::string text_;
public:
  explicit String(const std::string &text);
  explicit String(int);
  char charAt(int) const;
  Ref<String> substring(int) const;
  const std::string& getText() const;
  int size() const;
  void append(std::string const& tail);
  void append(char c);
  int length() const;
  friend std::ostream& zxing::operator << (std::ostream& out, String const& s);
};

}

#endif // __COMMON__STRING_H__

// file: zxing/common/BitSource.h

#ifndef __BIT_SOURCE_H__
// #define __BIT_SOURCE_H__

/*
 *  BitSource.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Array.h>

namespace zxing {
/**
 * <p>This provides an easy abstraction to read bits at a time from a sequence of bytes, where the
 * number of bits read is not often a multiple of 8.</p>
 *
 * <p>This class is not thread-safe.</p>
 *
 * @author srowen@google.com (Sean Owen)
 * @author christian.brunschen@gmail.com (Christian Brunschen)
 */
class BitSource : public Counted {
  typedef char byte;
private:
  ArrayRef<byte> bytes_;
  int byteOffset_;
  int bitOffset_;
public:
  /**
   * @param bytes bytes from which this will read bits. Bits will be read from the first byte first.
   * Bits are read within a byte from most-significant to least-significant bit.
   */
  BitSource(ArrayRef<byte> &bytes) :
      bytes_(bytes), byteOffset_(0), bitOffset_(0) {
  }

  int getBitOffset() {
    return bitOffset_;
  }

  int getByteOffset() {
    return byteOffset_;
  }

  /**
   * @param numBits number of bits to read
   * @return int representing the bits read. The bits will appear as the least-significant
   *         bits of the int
   * @throws IllegalArgumentException if numBits isn't in [1,32]
   */
  int readBits(int numBits);

  /**
   * @return number of bits that can be read successfully
   */
  int available();
};

}

#endif // __BIT_SOURCE_H__

// file: zxing/common/DecoderResult.h

#ifndef __DECODER_RESULT_H__
// #define __DECODER_RESULT_H__

/*
 *  DecoderResult.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <string>
// #include <zxing/common/Str.h>

namespace zxing {

class DecoderResult : public Counted {
private:
  ArrayRef<char> rawBytes_;
  Ref<String> text_;
  ArrayRef< ArrayRef<char> > byteSegments_;
  std::string ecLevel_;

public:
  DecoderResult(ArrayRef<char> rawBytes,
                Ref<String> text,
                ArrayRef< ArrayRef<char> >& byteSegments,
                std::string const& ecLevel);

  DecoderResult(ArrayRef<char> rawBytes, Ref<String> text);

  ArrayRef<char> getRawBytes();
  Ref<String> getText();
};

}

#endif // __DECODER_RESULT_H__

// file: zxing/common/PerspectiveTransform.h

#ifndef __PERSPECTIVE_TANSFORM_H__
// #define __PERSPECTIVE_TANSFORM_H__

/*
 *  PerspectiveTransform.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <vector>

namespace zxing {
class PerspectiveTransform : public Counted {
private:
  float a11, a12, a13, a21, a22, a23, a31, a32, a33;
  PerspectiveTransform(float a11, float a21, float a31, float a12, float a22, float a32, float a13, float a23,
                       float a33);

public:
  static Ref<PerspectiveTransform>
  quadrilateralToQuadrilateral(float x0, float y0, float x1, float y1, float x2, float y2, float x3, float y3,
                               float x0p, float y0p, float x1p, float y1p, float x2p, float y2p, float x3p, float y3p);
  static Ref<PerspectiveTransform> squareToQuadrilateral(float x0, float y0, float x1, float y1, float x2, float y2,
      float x3, float y3);
  static Ref<PerspectiveTransform> quadrilateralToSquare(float x0, float y0, float x1, float y1, float x2, float y2,
      float x3, float y3);
  Ref<PerspectiveTransform> buildAdjoint();
  Ref<PerspectiveTransform> times(Ref<PerspectiveTransform> other);
  void transformPoints(std::vector<float> &points);

  friend std::ostream& operator<<(std::ostream& out, const PerspectiveTransform &pt);
};
}

#endif // __PERSPECTIVE_TANSFORM_H__

// file: zxing/ResultPoint.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __RESULT_POINT_H__
// #define __RESULT_POINT_H__

/*
 *  ResultPoint.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <vector>

namespace zxing {

class ResultPoint : public Counted {
protected:
  const float posX_;
  const float posY_;

public:
  ResultPoint();
  ResultPoint(float x, float y);
  ResultPoint(int x, int y);
  virtual ~ResultPoint();

  virtual float getX() const;
  virtual float getY() const;

  bool equals(Ref<ResultPoint> other);

  static void orderBestPatterns(std::vector<Ref<ResultPoint> > &patterns);
  static float distance(Ref<ResultPoint> point1, Ref<ResultPoint> point2);
  static float distance(float x1, float x2, float y1, float y2);

private:
  static float crossProductZ(Ref<ResultPoint> pointA, Ref<ResultPoint> pointB, Ref<ResultPoint> pointC);
};

}

#endif // __RESULT_POINT_H__

// file: zxing/common/DetectorResult.h

#ifndef __DETECTOR_RESULT_H__
// #define __DETECTOR_RESULT_H__

/*
 *  DetectorResult.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/ResultPoint.h>

namespace zxing {

class DetectorResult : public Counted {
private:
  Ref<BitMatrix> bits_;
  ArrayRef< Ref<ResultPoint> > points_;

public:
  DetectorResult(Ref<BitMatrix> bits, ArrayRef< Ref<ResultPoint> > points);
  Ref<BitMatrix> getBits();
  ArrayRef< Ref<ResultPoint> > getPoints();
};

}

#endif // __DETECTOR_RESULT_H__

// file: zxing/common/Point.h

#ifndef __POINT_H__
// #define __POINT_H__

/*
 *  Point.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

namespace zxing {
class PointI {
public:
  int x;
  int y;
};

class Point {
public:
  Point() : x(0.0f), y(0.0f) {};
  Point(float x_, float y_) : x(x_), y(y_) {};

  float x;
  float y;
};

class Line {
public:
  Line(Point start_, Point end_) : start(start_), end(end_) {};

  Point start;
  Point end;
};
}
#endif // POINT_H_

// file: zxing/LuminanceSource.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __LUMINANCESOURCE_H__
// #define __LUMINANCESOURCE_H__
/*
 *  LuminanceSource.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <string.h>

namespace zxing {

class LuminanceSource : public Counted {
 private:
  const int width;
  const int height;

 public:
  LuminanceSource(int width, int height);
  virtual ~LuminanceSource();

  int getWidth() const { return width; }
  int getHeight() const { return height; }

  // Callers take ownership of the returned memory and must call delete [] on it themselves.
  virtual ArrayRef<char> getRow(int y, ArrayRef<char> row) const = 0;
  virtual ArrayRef<char> getMatrix() const = 0;

  virtual bool isCropSupported() const;
  virtual Ref<LuminanceSource> crop(int left, int top, int width, int height) const;

  virtual bool isRotateSupported() const;

  virtual Ref<LuminanceSource> invert() const;

  virtual Ref<LuminanceSource> rotateCounterClockwise() const;

  operator std::string () const;
};

}

#endif /* LUMINANCESOURCE_H_ */

// file: zxing/Binarizer.h

#ifndef BINARIZER_H_
#define BINARIZER_H_

/*
 *  Binarizer.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/LuminanceSource.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Counted.h>

namespace zxing {

class Binarizer : public Counted {
 private:
  Ref<LuminanceSource> source_;

 public:
  Binarizer(Ref<LuminanceSource> source);
  virtual ~Binarizer();

  virtual Ref<BitArray> getBlackRow(int y, Ref<BitArray> row) = 0;
  virtual Ref<BitMatrix> getBlackMatrix() = 0;

  Ref<LuminanceSource> getLuminanceSource() const ;
  virtual Ref<Binarizer> createBinarizer(Ref<LuminanceSource> source) = 0;

  int getWidth() const;
  int getHeight() const;

};

}
#endif /* BINARIZER_H_ */

// file: zxing/common/GlobalHistogramBinarizer.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __GLOBALHISTOGRAMBINARIZER_H__
// #define __GLOBALHISTOGRAMBINARIZER_H__
/*
 *  GlobalHistogramBinarizer.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Binarizer.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Array.h>

namespace zxing {

class GlobalHistogramBinarizer : public Binarizer {
private:
  ArrayRef<char> luminances;
  ArrayRef<int> buckets;
public:
  GlobalHistogramBinarizer(Ref<LuminanceSource> source);
  virtual ~GlobalHistogramBinarizer();

  virtual Ref<BitArray> getBlackRow(int y, Ref<BitArray> row);
  virtual Ref<BitMatrix> getBlackMatrix();
  static int estimateBlackPoint(ArrayRef<int> const& buckets);
  Ref<Binarizer> createBinarizer(Ref<LuminanceSource> source);
private:
  void initArrays(int luminanceSize);
};

}

#endif /* GLOBALHISTOGRAMBINARIZER_H_ */

// file: zxing/common/GreyscaleLuminanceSource.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __GREYSCALE_LUMINANCE_SOURCE__
#define __GREYSCALE_LUMINANCE_SOURCE__
/*
 *  GreyscaleLuminanceSource.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/LuminanceSource.h>

namespace zxing {

class GreyscaleLuminanceSource : public LuminanceSource {

private:
  typedef LuminanceSource Super;
  ArrayRef<char> greyData_;
  const int dataWidth_;
  const int dataHeight_;
  const int left_;
  const int top_;
  bool inverse_;

public:
  GreyscaleLuminanceSource(ArrayRef<char> greyData, int dataWidth, int dataHeight, int left,
                           int top, int width, int height, bool inverse);

  ArrayRef<char> getRow(int y, ArrayRef<char> row) const;
  ArrayRef<char> getMatrix() const;

  bool isRotateSupported() const {
    return true;
  }

  Ref<LuminanceSource> rotateCounterClockwise() const;
};

}

#endif

// file: zxing/common/GreyscaleRotatedLuminanceSource.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __GREYSCALE_ROTATED_LUMINANCE_SOURCE__
#define __GREYSCALE_ROTATED_LUMINANCE_SOURCE__
/*
 *  GreyscaleRotatedLuminanceSource.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


// #include <zxing/LuminanceSource.h>

namespace zxing {

class GreyscaleRotatedLuminanceSource : public LuminanceSource {
 private:
  typedef LuminanceSource Super;
  ArrayRef<char> greyData_;
  const int dataWidth_;
  const int left_;
  const int top_;

public:
  GreyscaleRotatedLuminanceSource(ArrayRef<char> greyData, int dataWidth, int dataHeight,
      int left, int top, int width, int height);

  ArrayRef<char> getRow(int y, ArrayRef<char> row) const;
  ArrayRef<char> getMatrix() const;
};

}

#endif

// file: zxing/common/GridSampler.h

#ifndef __GRID_SAMPLER_H__
// #define __GRID_SAMPLER_H__

/*
 *  GridSampler.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/PerspectiveTransform.h>

namespace zxing {
class GridSampler {
private:
  static GridSampler gridSampler;
  GridSampler();

public:
  Ref<BitMatrix> sampleGrid(Ref<BitMatrix> image, int dimension, Ref<PerspectiveTransform> transform);
  Ref<BitMatrix> sampleGrid(Ref<BitMatrix> image, int dimensionX, int dimensionY, Ref<PerspectiveTransform> transform);

  Ref<BitMatrix> sampleGrid(Ref<BitMatrix> image, int dimension, float p1ToX, float p1ToY, float p2ToX, float p2ToY,
                            float p3ToX, float p3ToY, float p4ToX, float p4ToY, float p1FromX, float p1FromY, float p2FromX,
                            float p2FromY, float p3FromX, float p3FromY, float p4FromX, float p4FromY);
  static void checkAndNudgePoints(Ref<BitMatrix> image, std::vector<float> &points);
  static GridSampler &getInstance();
};
}

#endif // __GRID_SAMPLER_H__

// file: zxing/common/HybridBinarizer.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __HYBRIDBINARIZER_H__
// #define __HYBRIDBINARIZER_H__
/*
 *  HybridBinarizer.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <vector>
// #include <zxing/Binarizer.h>
// #include <zxing/common/GlobalHistogramBinarizer.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/common/BitMatrix.h>

namespace zxing {

	class HybridBinarizer : public GlobalHistogramBinarizer {
	 private:
    Ref<BitMatrix> matrix_;
	  Ref<BitArray> cached_row_;

	public:
		HybridBinarizer(Ref<LuminanceSource> source);
		virtual ~HybridBinarizer();

		virtual Ref<BitMatrix> getBlackMatrix();
		Ref<Binarizer> createBinarizer(Ref<LuminanceSource> source);
  private:
    // We'll be using one-D arrays because C++ can't dynamically allocate 2D
    // arrays
    ArrayRef<int> calculateBlackPoints(ArrayRef<char> luminances,
                                       int subWidth,
                                       int subHeight,
                                       int width,
                                       int height);
    void calculateThresholdForBlock(ArrayRef<char> luminances,
                                    int subWidth,
                                    int subHeight,
                                    int width,
                                    int height,
                                    ArrayRef<int> blackPoints,
                                    Ref<BitMatrix> const& matrix);
    void thresholdBlock(ArrayRef<char>luminances,
                        int xoffset,
                        int yoffset,
                        int threshold,
                        int stride,
                        Ref<BitMatrix> const& matrix);
	};

}

#endif

// file: zxing/common/reedsolomon/GenericGF.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  GenericGF.h
 *  zxing
 *
 *  Created by Lukas Stabe on 13/02/2012.
 *  Copyright 2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef GENERICGF_H
#define GENERICGF_H

// #include <vector>
// #include <zxing/common/Counted.h>

namespace zxing {
  class GenericGFPoly;

  class GenericGF : public Counted {

  private:
    std::vector<int> expTable;
    std::vector<int> logTable;
    Ref<GenericGFPoly> zero;
    Ref<GenericGFPoly> one;
    int size;
    int primitive;
    int generatorBase;
    bool initialized;

    void initialize();
    void checkInit();

  public:
    static Ref<GenericGF> AZTEC_DATA_12;
    static Ref<GenericGF> AZTEC_DATA_10;
    static Ref<GenericGF> AZTEC_DATA_8;
    static Ref<GenericGF> AZTEC_DATA_6;
    static Ref<GenericGF> AZTEC_PARAM;
    static Ref<GenericGF> QR_CODE_FIELD_256;
    static Ref<GenericGF> DATA_MATRIX_FIELD_256;
    static Ref<GenericGF> MAXICODE_FIELD_64;

    GenericGF(int primitive, int size, int b);

    Ref<GenericGFPoly> getZero();
    Ref<GenericGFPoly> getOne();
    int getSize();
    int getGeneratorBase();
    Ref<GenericGFPoly> buildMonomial(int degree, int coefficient);

    static int addOrSubtract(int a, int b);
    int exp(int a);
    int log(int a);
    int inverse(int a);
    int multiply(int a, int b);
  };
}

#endif //GENERICGF_H

// file: zxing/common/reedsolomon/GenericGFPoly.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  GenericGFPoly.h
 *  zxing
 *
 *  Created by Lukas Stabe on 13/02/2012.
 *  Copyright 2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef GENERICGFPOLY_H
#define GENERICGFPOLY_H

// #include <vector>
// #include <zxing/common/Array.h>
// #include <zxing/common/Counted.h>

namespace zxing {

class GenericGF;

class GenericGFPoly : public Counted {
private:
  GenericGF &field_;
  ArrayRef<int> coefficients_;

public:
  GenericGFPoly(GenericGF &field, ArrayRef<int> coefficients);
  ArrayRef<int> getCoefficients();
  int getDegree();
  bool isZero();
  int getCoefficient(int degree);
  int evaluateAt(int a);
  Ref<GenericGFPoly> addOrSubtract(Ref<GenericGFPoly> other);
  Ref<GenericGFPoly> multiply(Ref<GenericGFPoly> other);
  Ref<GenericGFPoly> multiply(int scalar);
  Ref<GenericGFPoly> multiplyByMonomial(int degree, int coefficient);
  std::vector<Ref<GenericGFPoly> > divide(Ref<GenericGFPoly> other);


};

}

#endif //GENERICGFPOLY_H

// file: zxing/common/reedsolomon/ReedSolomonDecoder.h

#ifndef __REED_SOLOMON_DECODER_H__
// #define __REED_SOLOMON_DECODER_H__

/*
 *  ReedSolomonDecoder.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <memory>
// #include <vector>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/reedsolomon/GenericGFPoly.h>
// #include <zxing/common/reedsolomon/GenericGF.h>

namespace zxing {
class GenericGFPoly;
class GenericGF;

class ReedSolomonDecoder {
private:
  Ref<GenericGF> field;
public:
  ReedSolomonDecoder(Ref<GenericGF> fld);
  ~ReedSolomonDecoder();
  void decode(ArrayRef<int> received, int twoS);
  std::vector<Ref<GenericGFPoly> > runEuclideanAlgorithm(Ref<GenericGFPoly> a, Ref<GenericGFPoly> b, int R);

private:
  ArrayRef<int> findErrorLocations(Ref<GenericGFPoly> errorLocator);
  ArrayRef<int> findErrorMagnitudes(Ref<GenericGFPoly> errorEvaluator, ArrayRef<int> errorLocations);
};
}

#endif // __REED_SOLOMON_DECODER_H__

// file: zxing/common/reedsolomon/ReedSolomonException.h

#ifndef __REED_SOLOMON_EXCEPTION_H__
// #define __REED_SOLOMON_EXCEPTION_H__

/*
 *  ReedSolomonException.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Exception.h>

namespace zxing {
class ReedSolomonException : public Exception {
public:
  ReedSolomonException(const char *msg) throw();
  ~ReedSolomonException() throw();
};
}

#endif // __REED_SOLOMON_EXCEPTION_H__

// file: zxing/BarcodeFormat.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __BARCODE_FORMAT_H__
// #define __BARCODE_FORMAT_H__

/*
 *  BarcodeFormat.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

namespace zxing {

class BarcodeFormat {
public:
  // if you update the enum, update BarcodeFormat.cpp

  enum Value {
    NONE,
    AZTEC,
    CODABAR,
    CODE_39,
    CODE_93,
    CODE_128,
    DATA_MATRIX,
    EAN_8,
    EAN_13,
    ITF,
    MAXICODE,
    PDF_417,
    QR_CODE,
    RSS_14,
    RSS_EXPANDED,
    UPC_A,
    UPC_E,
    UPC_EAN_EXTENSION
  };

  BarcodeFormat(Value v) : value(v) {}
  const Value value;
  operator Value () const {return value;}

  static char const* barcodeFormatNames[];
};

}

#endif // __BARCODE_FORMAT_H__

// file: zxing/BinaryBitmap.h

#ifndef __BINARYBITMAP_H__
// #define __BINARYBITMAP_H__

/*
 *  BinaryBitmap.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/Binarizer.h>

namespace zxing {

	class BinaryBitmap : public Counted {
	private:
		Ref<Binarizer> binarizer_;

	public:
		BinaryBitmap(Ref<Binarizer> binarizer);
		virtual ~BinaryBitmap();

		Ref<BitArray> getBlackRow(int y, Ref<BitArray> row);
		Ref<BitMatrix> getBlackMatrix();

		Ref<LuminanceSource> getLuminanceSource() const;

		int getWidth() const;
		int getHeight() const;

		bool isRotateSupported() const;
		Ref<BinaryBitmap> rotateCounterClockwise();

		bool isCropSupported() const;
		Ref<BinaryBitmap> crop(int left, int top, int width, int height);

	};

}

#endif /* BINARYBITMAP_H_ */

// file: zxing/ResultPointCallback.h

#ifndef __RESULT_POINT_CALLBACK_H__
// #define __RESULT_POINT_CALLBACK_H__

/*
 *  ResultPointCallback.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>

namespace zxing {

class ResultPoint;

class ResultPointCallback : public Counted {
protected:
  ResultPointCallback() {}
public:
  virtual void foundPossibleResultPoint(ResultPoint const& point) = 0;
  virtual ~ResultPointCallback();
};

}

#endif // __RESULT_POINT_CALLBACK_H__

// file: zxing/DecodeHints.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __DECODEHINTS_H_
#define __DECODEHINTS_H_
/*
 *  DecodeHintType.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/BarcodeFormat.h>
// #include <zxing/ResultPointCallback.h>

namespace zxing {

typedef unsigned int DecodeHintType;
class DecodeHints;
DecodeHints operator | (DecodeHints const&, DecodeHints const&);

class DecodeHints {
 private:
  DecodeHintType hints;
  Ref<ResultPointCallback> callback;

 public:
  static const DecodeHintType AZTEC_HINT = 1 << BarcodeFormat::AZTEC;
  static const DecodeHintType CODABAR_HINT = 1 << BarcodeFormat::CODABAR;
  static const DecodeHintType CODE_39_HINT = 1 << BarcodeFormat::CODE_39;
  static const DecodeHintType CODE_93_HINT = 1 << BarcodeFormat::CODE_93;
  static const DecodeHintType CODE_128_HINT = 1 << BarcodeFormat::CODE_128;
  static const DecodeHintType DATA_MATRIX_HINT = 1 << BarcodeFormat::DATA_MATRIX;
  static const DecodeHintType EAN_8_HINT = 1 << BarcodeFormat::EAN_8;
  static const DecodeHintType EAN_13_HINT = 1 << BarcodeFormat::EAN_13;
  static const DecodeHintType ITF_HINT = 1 << BarcodeFormat::ITF;
  static const DecodeHintType MAXICODE_HINT = 1 << BarcodeFormat::MAXICODE;
  static const DecodeHintType PDF_417_HINT = 1 << BarcodeFormat::PDF_417;
  static const DecodeHintType QR_CODE_HINT = 1 << BarcodeFormat::QR_CODE;
  static const DecodeHintType RSS_14_HINT = 1 << BarcodeFormat::RSS_14;
  static const DecodeHintType RSS_EXPANDED_HINT = 1 << BarcodeFormat::RSS_EXPANDED;
  static const DecodeHintType UPC_A_HINT = 1 << BarcodeFormat::UPC_A;
  static const DecodeHintType UPC_E_HINT = 1 << BarcodeFormat::UPC_E;
  static const DecodeHintType UPC_EAN_EXTENSION_HINT = 1 << BarcodeFormat::UPC_EAN_EXTENSION;

  static const DecodeHintType TRYHARDER_HINT = 1 << 31;
  static const DecodeHintType CHARACTER_SET = 1 << 30;
  // static const DecodeHintType ALLOWED_LENGTHS = 1 << 29;
  // static const DecodeHintType ASSUME_CODE_39_CHECK_DIGIT = 1 << 28;
  static const DecodeHintType  ASSUME_GS1 = 1 << 27;
  // static const DecodeHintType NEED_RESULT_POINT_CALLBACK = 1 << 26;

  static const DecodeHints PRODUCT_HINT;
  static const DecodeHints ONED_HINT;
  static const DecodeHints DEFAULT_HINT;

  DecodeHints();
  DecodeHints(DecodeHintType init);

  void addFormat(BarcodeFormat toadd);
  bool containsFormat(BarcodeFormat tocheck) const;
  bool isEmpty() const {return (hints==0);}
  void clear() {hints=0;}
  void setTryHarder(bool toset);
  bool getTryHarder() const;

  void setResultPointCallback(Ref<ResultPointCallback> const&);
  Ref<ResultPointCallback> getResultPointCallback() const;

  friend DecodeHints operator | (DecodeHints const&, DecodeHints const&);
};

}

#endif

// file: zxing/Result.h

#ifndef __RESULT_H__
// #define __RESULT_H__

/*
 *  Result.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <string>
// #include <zxing/common/Array.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Str.h>
// #include <zxing/ResultPoint.h>
// #include <zxing/BarcodeFormat.h>

namespace zxing {

class Result : public Counted {
private:
  Ref<String> text_;
  ArrayRef<char> rawBytes_;
  ArrayRef< Ref<ResultPoint> > resultPoints_;
  BarcodeFormat format_;

public:
  Result(Ref<String> text,
         ArrayRef<char> rawBytes,
         ArrayRef< Ref<ResultPoint> > resultPoints,
         BarcodeFormat format);
  ~Result();
  Ref<String> getText();
  ArrayRef<char> getRawBytes();
  ArrayRef< Ref<ResultPoint> > const& getResultPoints() const;
  ArrayRef< Ref<ResultPoint> >& getResultPoints();
  BarcodeFormat getBarcodeFormat() const;

  friend std::ostream& operator<<(std::ostream &out, Result& result);
};

}
#endif // __RESULT_H__

// file: zxing/Reader.h

#ifndef __READER_H__
// #define __READER_H__

/*
 *  Reader.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/BinaryBitmap.h>
// #include <zxing/Result.h>
// #include <zxing/DecodeHints.h>

namespace zxing {

 class Reader : public Counted {
  protected:
   Reader() {}
  public:
   virtual Ref<Result> decode(Ref<BinaryBitmap> image);
   virtual Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints) = 0;
   virtual ~Reader();
};

}

#endif // __READER_H__

// file: zxing/MultiFormatReader.h

#ifndef __MULTI_FORMAT_READER_H__
// #define __MULTI_FORMAT_READER_H__

/*
 *  MultiFormatBarcodeReader.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


// #include <zxing/Reader.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/Result.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
  class MultiFormatReader : public Reader {
  private:
    Ref<Result> decodeInternal(Ref<BinaryBitmap> image);

    std::vector<Ref<Reader> > readers_;
    DecodeHints hints_;

  public:
    MultiFormatReader();

    Ref<Result> decode(Ref<BinaryBitmap> image);
    Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints);
    Ref<Result> decodeWithState(Ref<BinaryBitmap> image);
    void setHints(DecodeHints hints);
    ~MultiFormatReader();
  };
}

#endif

// file: zxing/ReaderException.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __READER_EXCEPTION_H__
// #define __READER_EXCEPTION_H__

/*
 *  ReaderException.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Exception.h>

namespace zxing {

class ReaderException : public Exception {
 public:
  ReaderException() throw() {}
  ReaderException(char const* msg) throw() : Exception(msg) {}
  ~ReaderException() throw() {}
};

}

#endif // __READER_EXCEPTION_H__

// file: zxing/datamatrix/decoder/Decoder.h

#ifndef __DECODER_DM_H__
// #define __DECODER_DM_H__

/*
 *  Decoder.h
 *  zxing
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/reedsolomon/ReedSolomonDecoder.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/DecoderResult.h>
// #include <zxing/common/BitMatrix.h>


namespace zxing {
    namespace datamatrix {

        class Decoder {
        private:
            ReedSolomonDecoder rsDecoder_;

            void correctErrors(ArrayRef<char> bytes, int numDataCodewords);

        public:
            Decoder();

            Ref<DecoderResult> decode(Ref<BitMatrix> bits);
        };

    }
}

#endif // __DECODER_DM_H__

// file: zxing/datamatrix/DataMatrixReader.h

#ifndef __DATA_MATRIX_READER_H__
// #define __DATA_MATRIX_READER_H__

/*
 *  DataMatrixReader.h
 *  zxing
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Reader.h>
// #include <zxing/DecodeHints.h>
// #include <zxing/datamatrix/decoder/Decoder.h>

namespace zxing {
namespace datamatrix {

class DataMatrixReader : public Reader {
private:
  Decoder decoder_;

public:
  DataMatrixReader();
  virtual Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints);
  virtual ~DataMatrixReader();

};

}
}

#endif // __DATA_MATRIX_READER_H__

// file: zxing/datamatrix/Version.h

#ifndef __VERSION_H__
// #define __VERSION_H__

/*
 *  Version.h
 *  zxing
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Counted.h>
// #include <vector>

namespace zxing {
namespace datamatrix {

class ECB {
private:
  int count_;
  int dataCodewords_;
public:
  ECB(int count, int dataCodewords);
  int getCount();
  int getDataCodewords();
};

class ECBlocks {
private:
  int ecCodewords_;
  std::vector<ECB*> ecBlocks_;
public:
  ECBlocks(int ecCodewords, ECB *ecBlocks);
  ECBlocks(int ecCodewords, ECB *ecBlocks1, ECB *ecBlocks2);
  int getECCodewords();
  std::vector<ECB*>& getECBlocks();
  ~ECBlocks();
};

class Version : public Counted {
private:
  int versionNumber_;
  int symbolSizeRows_;
  int symbolSizeColumns_;
  int dataRegionSizeRows_;
  int dataRegionSizeColumns_;
  ECBlocks* ecBlocks_;
  int totalCodewords_;
  Version(int versionNumber, int symbolSizeRows, int symbolSizeColumns, int dataRegionSizeRows,
		  int dataRegionSizeColumns, ECBlocks *ecBlocks);

public:
  static std::vector<Ref<Version> > VERSIONS;

  ~Version();
  int getVersionNumber();
  int getSymbolSizeRows();
  int getSymbolSizeColumns();
  int getDataRegionSizeRows();
  int getDataRegionSizeColumns();
  int getTotalCodewords();
  ECBlocks* getECBlocks();
  static int  buildVersions();
  Ref<Version> getVersionForDimensions(int numRows, int numColumns);

private:
  Version(const Version&);
  Version & operator=(const Version&);
};
}
}

#endif // __VERSION_H__

// file: zxing/datamatrix/decoder/BitMatrixParser.h

#ifndef __BIT_MATRIX_PARSER_DM_H__
// #define __BIT_MATRIX_PARSER_DM_H__

/*
 *  BitMatrixParser.h
 *  zxing
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/datamatrix/Version.h>

namespace zxing {
namespace datamatrix {

class BitMatrixParser : public Counted {
private:
  Ref<BitMatrix> bitMatrix_;
  Ref<Version> parsedVersion_;
  Ref<BitMatrix> readBitMatrix_;

  int copyBit(size_t x, size_t y, int versionBits);

public:
  BitMatrixParser(Ref<BitMatrix> bitMatrix);
  Ref<Version> readVersion(Ref<BitMatrix> bitMatrix);
  ArrayRef<char> readCodewords();
  bool readModule(int row, int column, int numRows, int numColumns);

private:
  int readUtah(int row, int column, int numRows, int numColumns);
  int readCorner1(int numRows, int numColumns);
  int readCorner2(int numRows, int numColumns);
  int readCorner3(int numRows, int numColumns);
  int readCorner4(int numRows, int numColumns);
  Ref<BitMatrix> extractDataRegion(Ref<BitMatrix> bitMatrix);
};

}
}

#endif // __BIT_MATRIX_PARSER_DM_H__

// file: zxing/datamatrix/decoder/DataBlock.h

#ifndef __DATA_BLOCK_DM_H__
// #define __DATA_BLOCK_DM_H__

/*
 *  DataBlock.h
 *  zxing
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <vector>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/datamatrix/Version.h>

namespace zxing {
namespace datamatrix {

class DataBlock : public Counted {
private:
  int numDataCodewords_;
  ArrayRef<char> codewords_;

  DataBlock(int numDataCodewords, ArrayRef<char> codewords);

public:
  static std::vector<Ref<DataBlock> > getDataBlocks(ArrayRef<char> rawCodewords, Version *version);

  int getNumDataCodewords();
  ArrayRef<char> getCodewords();
};

}
}

#endif // __DATA_BLOCK_DM_H__

// file: zxing/datamatrix/decoder/DecodedBitStreamParser.h

#ifndef __DECODED_BIT_STREAM_PARSER_DM_H__
// #define __DECODED_BIT_STREAM_PARSER_DM_H__

/*
 *  DecodedBitStreamParser.h
 *  zxing
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <string>
// #include <sstream>
// #include <zxing/common/Array.h>
// #include <zxing/common/BitSource.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/DecoderResult.h>


namespace zxing {
namespace datamatrix {

class DecodedBitStreamParser {
private:
  static const int PAD_ENCODE = 0;  // Not really an encoding
  static const int ASCII_ENCODE = 1;
  static const int C40_ENCODE = 2;
  static const int TEXT_ENCODE = 3;
  static const int ANSIX12_ENCODE = 4;
  static const int EDIFACT_ENCODE = 5;
  static const int BASE256_ENCODE = 6;

  /**
   * See ISO 16022:2006, Annex C Table C.1
   * The C40 Basic Character Set (*'s used for placeholders for the shift values)
   */
  static const char C40_BASIC_SET_CHARS[];

  static const char C40_SHIFT2_SET_CHARS[];
  /**
   * See ISO 16022:2006, Annex C Table C.2
   * The Text Basic Character Set (*'s used for placeholders for the shift values)
   */
  static const char TEXT_BASIC_SET_CHARS[];

  static const char TEXT_SHIFT3_SET_CHARS[];
  /**
   * See ISO 16022:2006, 5.2.3 and Annex C, Table C.2
   */
  int decodeAsciiSegment(Ref<BitSource> bits, std::ostringstream &result, std::ostringstream &resultTrailer);
  /**
   * See ISO 16022:2006, 5.2.5 and Annex C, Table C.1
   */
  void decodeC40Segment(Ref<BitSource> bits, std::ostringstream &result);
  /**
   * See ISO 16022:2006, 5.2.6 and Annex C, Table C.2
   */
  void decodeTextSegment(Ref<BitSource> bits, std::ostringstream &result);
  /**
   * See ISO 16022:2006, 5.2.7
   */
  void decodeAnsiX12Segment(Ref<BitSource> bits, std::ostringstream &result);
  /**
   * See ISO 16022:2006, 5.2.8 and Annex C Table C.3
   */
  void decodeEdifactSegment(Ref<BitSource> bits, std::ostringstream &result);
  /**
   * See ISO 16022:2006, 5.2.9 and Annex B, B.2
   */
  void decodeBase256Segment(Ref<BitSource> bits, std::ostringstream &result, std::vector<char> byteSegments);

  void parseTwoBytes(int firstByte, int secondByte, int* result);
  /**
   * See ISO 16022:2006, Annex B, B.2
   */
  char unrandomize255State(int randomizedBase256Codeword,
                           int base256CodewordPosition) {
    int pseudoRandomNumber = ((149 * base256CodewordPosition) % 255) + 1;
    int tempVariable = randomizedBase256Codeword - pseudoRandomNumber;
    return (char) (tempVariable >= 0 ? tempVariable : (tempVariable + 256));
  };
  void append(std::ostream &ost, const char *bufIn, size_t nIn, const char *src);

public:
  DecodedBitStreamParser() { };
  Ref<DecoderResult> decode(ArrayRef<char> bytes);
};

}
}

#endif // __DECODED_BIT_STREAM_PARSER_DM_H__

// file: zxing/datamatrix/detector/CornerPoint.h

#ifndef __CORNER_FINDER_H__
// #define __CORNER_FINDER_H__

/*
 *  CornerPoint.h
 *  zxing
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ResultPoint.h>
// #include <cmath>

namespace zxing {
	namespace datamatrix {

		class CornerPoint : public ResultPoint {
		private:
			int counter_;

		public:
			CornerPoint(float posX, float posY);
			int getCount() const;
			void incrementCount();
			bool equals(Ref<CornerPoint> other) const;
		};
	}
}

#endif // __CORNER_FINDER_H__

// file: zxing/datamatrix/detector/Detector.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __DETECTOR_H__
// #define __DETECTOR_H__

/*
 *  Detector.h
 *  zxing
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/DetectorResult.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/PerspectiveTransform.h>
// #include <zxing/common/detector/WhiteRectangleDetector.h>

namespace zxing {
namespace datamatrix {

class ResultPointsAndTransitions: public Counted {
  private:
    Ref<ResultPoint> to_;
    Ref<ResultPoint> from_;
    int transitions_;

  public:
    ResultPointsAndTransitions();
    ResultPointsAndTransitions(Ref<ResultPoint> from, Ref<ResultPoint> to, int transitions);
    Ref<ResultPoint> getFrom();
    Ref<ResultPoint> getTo();
    int getTransitions();
};

class Detector: public Counted {
  private:
    Ref<BitMatrix> image_;

  protected:
    Ref<BitMatrix> sampleGrid(Ref<BitMatrix> image, int dimensionX, int dimensionY,
        Ref<PerspectiveTransform> transform);

    void insertionSort(std::vector<Ref<ResultPointsAndTransitions> >& vector);

    Ref<ResultPoint> correctTopRightRectangular(Ref<ResultPoint> bottomLeft,
        Ref<ResultPoint> bottomRight, Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight,
        int dimensionTop, int dimensionRight);
    Ref<ResultPoint> correctTopRight(Ref<ResultPoint> bottomLeft, Ref<ResultPoint> bottomRight,
        Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight, int dimension);
    bool isValid(Ref<ResultPoint> p);
    int distance(Ref<ResultPoint> a, Ref<ResultPoint> b);
    Ref<ResultPointsAndTransitions> transitionsBetween(Ref<ResultPoint> from, Ref<ResultPoint> to);
    int min(int a, int b) {
      return a > b ? b : a;
    }
    /**
     * Ends up being a bit faster than round(). This merely rounds its
     * argument to the nearest int, where x.5 rounds up.
     */
    int round(float d) {
      return (int) (d + 0.5f);
    }

  public:
    Ref<BitMatrix> getImage();
    Detector(Ref<BitMatrix> image);

    virtual Ref<PerspectiveTransform> createTransform(Ref<ResultPoint> topLeft,
        Ref<ResultPoint> topRight, Ref<ResultPoint> bottomLeft, Ref<ResultPoint> bottomRight,
        int dimensionX, int dimensionY);

    Ref<DetectorResult> detect();

  private:
    int compare(Ref<ResultPointsAndTransitions> a, Ref<ResultPointsAndTransitions> b);
};

}
}

#endif // __DETECTOR_H__

// file: zxing/datamatrix/detector/DetectorException.h

/*
 * DetectorException.h
 *
 *  Created on: Aug 26, 2011
 *      Author: luiz
 */

#ifndef DETECTOREXCEPTION_H_
#define DETECTOREXCEPTION_H_

// #include <zxing/Exception.h>

namespace zxing {
namespace datamatrix {

class DetectorException : public Exception {
  public:
    DetectorException(const char *msg);
    virtual ~DetectorException() throw();
};
} /* namespace nexxera */
} /* namespace zxing */
#endif /* DETECTOREXCEPTION_H_ */

// file: zxing/oned/OneDReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __ONED_READER_H__
// #define __ONED_READER_H__

/*
 *  OneDReader.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Reader.h>

namespace zxing {
    namespace oned {

        class OneDReader : public Reader {
        private:
            Ref<Result> doDecode(Ref<BinaryBitmap> image, DecodeHints hints);

        protected:
            static const int INTEGER_MATH_SHIFT = 8;

            struct Range {
            private:
                int data[2];
            public:
                Range() {}
                Range(int zero, int one) {
                    data[0] = zero;
                    data[1] = one;
                }
                int& operator [] (int index) {
                    return data[index];
                }
                int const& operator [] (int index) const {
                    return data[index];
                }
            };

            static int patternMatchVariance(std::vector<int>& counters,
                                            std::vector<int> const& pattern,
                                            int maxIndividualVariance);
            static int patternMatchVariance(std::vector<int>& counters,
                                            int const pattern[],
                                            int maxIndividualVariance);

        protected:
            static const int PATTERN_MATCH_RESULT_SCALE_FACTOR = 1 << INTEGER_MATH_SHIFT;

        public:

            OneDReader();
            virtual Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints);

            // Implementations must not throw any exceptions. If a barcode is not found on this row,
            // a empty ref should be returned e.g. return Ref<Result>();
            virtual Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row) = 0;

            static void recordPattern(Ref<BitArray> row,
                                      int start,
                                      std::vector<int>& counters);
            virtual ~OneDReader();
        };

    }
}

#endif

// file: zxing/oned/CodaBarReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __CODA_BAR_READER_H__
// #define __CODA_BAR_READER_H__
/*
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/OneDReader.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/Result.h>

namespace zxing {
namespace oned {

class CodaBarReader : public OneDReader {
private:
  static const int MAX_ACCEPTABLE;
  static const int PADDING;

  // Keep some instance variables to avoid reallocations
  std::string decodeRowResult;
  std::vector<int> counters;
  int counterLength;

public:
  CodaBarReader();

  Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);

  void validatePattern(int start);

private:
  void setCounters(Ref<BitArray> row);
  void counterAppend(int e);
  int findStartPattern();

  static bool arrayContains(char const array[], char key);

  int toNarrowWidePattern(int position);
};

}
}

#endif

// file: zxing/oned/Code128Reader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __CODE_128_READER_H__
// #define __CODE_128_READER_H__
/*
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/OneDReader.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/Result.h>

namespace zxing {
namespace oned {

class Code128Reader : public OneDReader {
private:
  static const int MAX_AVG_VARIANCE;
  static const int MAX_INDIVIDUAL_VARIANCE;

  static std::vector<int> findStartPattern(Ref<BitArray> row);
  static int decodeCode(Ref<BitArray> row,
                        std::vector<int>& counters,
                        int rowOffset);

public:
  Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);
  Code128Reader();
  ~Code128Reader();

  BarcodeFormat getBarcodeFormat();
};

}
}

#endif

// file: zxing/oned/Code39Reader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __CODE_39_READER_H__
// #define __CODE_39_READER_H__
/*
 *  Code39Reader.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/OneDReader.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/Result.h>

namespace zxing {
namespace oned {

/**
 * <p>Decodes Code 39 barcodes. This does not support "Full ASCII Code 39" yet.</p>
 * Ported form Java (author Sean Owen)
 * @author Lukasz Warchol
 */
class Code39Reader : public OneDReader {
private:
  bool usingCheckDigit;
  bool extendedMode;
  std::string decodeRowResult;
  std::vector<int> counters;

  void init(bool usingCheckDigit = false, bool extendedMode = false);

  static std::vector<int> findAsteriskPattern(Ref<BitArray> row,
                                              std::vector<int>& counters);
  static int toNarrowWidePattern(std::vector<int>& counters);
  static char patternToChar(int pattern);
  static Ref<String> decodeExtended(std::string encoded);

  void append(char* s, char c);

public:
  Code39Reader();
  Code39Reader(bool usingCheckDigit_);
  Code39Reader(bool usingCheckDigit_, bool extendedMode_);

  Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);
};

}
}

#endif

// file: zxing/oned/Code93Reader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __CODE_93_READER_H__
// #define __CODE_93_READER_H__
/*
 *  Code93Reader.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/OneDReader.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/Result.h>

namespace zxing {
namespace oned {

/**
 * <p>Decodes Code 93 barcodes. This does not support "Full ASCII Code 93" yet.</p>
 * Ported form Java (author Sean Owen)
 * @author Lukasz Warchol
 */
class Code93Reader : public OneDReader {
public:
  Code93Reader();
  Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);

private:
  std::string decodeRowResult;
  std::vector<int> counters;

  Range findAsteriskPattern(Ref<BitArray> row);

  static int toPattern(std::vector<int>& counters);
  static char patternToChar(int pattern);
  static Ref<String> decodeExtended(std::string const& encoded);
  static void checkChecksums(std::string const& result);
  static void checkOneChecksum(std::string const& result,
                               int checkPosition,
                               int weightMax);
};

}
}

#endif

// file: zxing/oned/UPCEANReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __UPC_EAN_READER_H__
// #define __UPC_EAN_READER_H__

/*
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/OneDReader.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/Result.h>

namespace zxing {
    namespace oned {

        class UPCEANReader : public OneDReader {
        private:
            std::string decodeRowStringBuffer;
            // UPCEANExtensionSupport extensionReader;
            // EANManufacturerOrgSupport eanManSupport;

            static const int MAX_AVG_VARIANCE;
            static const int MAX_INDIVIDUAL_VARIANCE;

            static Range findStartGuardPattern(Ref<BitArray> row);

            virtual Range decodeEnd(Ref<BitArray> row, int endStart);

            static bool checkStandardUPCEANChecksum(Ref<String> const& s);

            static Range findGuardPattern(Ref<BitArray> row,
                                          int rowOffset,
                                          bool whiteFirst,
                                          std::vector<int> const& pattern,
                                          std::vector<int>& counters);


        protected:
            static const std::vector<int> START_END_PATTERN;
            static const std::vector<int> MIDDLE_PATTERN;

            static const std::vector<int const*> L_PATTERNS;
            static const std::vector<int const*> L_AND_G_PATTERNS;

            static Range findGuardPattern(Ref<BitArray> row,
                                          int rowOffset,
                                          bool whiteFirst,
                                          std::vector<int> const& pattern);

        public:
            UPCEANReader();

            virtual int decodeMiddle(Ref<BitArray> row,
                                     Range const& startRange,
                                     std::string& resultString) = 0;

            virtual Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);
            virtual Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row, Range const& range);

            static int decodeDigit(Ref<BitArray> row,
                                   std::vector<int>& counters,
                                   int rowOffset,
                                   std::vector<int const*> const& patterns);

            virtual bool checkChecksum(Ref<String> const& s);

            virtual BarcodeFormat getBarcodeFormat() = 0;
            virtual ~UPCEANReader();

            friend class MultiFormatUPCEANReader;
        };

    }
}

#endif

// file: zxing/oned/EAN13Reader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __EAN_13_READER_H__
// #define __EAN_13_READER_H__

/*
 *  EAN13Reader.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/UPCEANReader.h>
// #include <zxing/Result.h>

namespace zxing {
namespace oned {

class EAN13Reader : public UPCEANReader {
private:
  std::vector<int> decodeMiddleCounters;
  static void determineFirstDigit(std::string& resultString,
                                  int lgPatternFound);

public:
  EAN13Reader();

  int decodeMiddle(Ref<BitArray> row,
                   Range const& startRange,
                   std::string& resultString);

  BarcodeFormat getBarcodeFormat();
};

}
}

#endif

// file: zxing/oned/EAN8Reader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __EAN_8_READER_H__
// #define __EAN_8_READER_H__

/*
 *  EAN8Reader.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/UPCEANReader.h>
// #include <zxing/Result.h>

namespace zxing {
namespace oned {

class EAN8Reader : public UPCEANReader {
 private:
  std::vector<int> decodeMiddleCounters;

 public:
  EAN8Reader();

  int decodeMiddle(Ref<BitArray> row,
                   Range const& startRange,
                   std::string& resultString);

  BarcodeFormat getBarcodeFormat();
};

}
}

#endif

// file: zxing/oned/ITFReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __ITF_READER_H__
// #define __ITF_READER_H__

/*
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/OneDReader.h>
// #include <zxing/common/BitArray.h>
// #include <zxing/Result.h>

namespace zxing {
namespace oned {

class ITFReader : public OneDReader {
private:
  enum {MAX_AVG_VARIANCE = (unsigned int) (PATTERN_MATCH_RESULT_SCALE_FACTOR * 420/1000)};
  enum {MAX_INDIVIDUAL_VARIANCE = (int) (PATTERN_MATCH_RESULT_SCALE_FACTOR * 780/1000)};
  // Stores the actual narrow line width of the image being decoded.
  int narrowLineWidth;

  Range decodeStart(Ref<BitArray> row);
  Range decodeEnd(Ref<BitArray> row);
  static void decodeMiddle(Ref<BitArray> row, int payloadStart, int payloadEnd, std::string& resultString);
  void validateQuietZone(Ref<BitArray> row, int startPattern);
  static int skipWhiteSpace(Ref<BitArray> row);

  static Range findGuardPattern(Ref<BitArray> row, int rowOffset, std::vector<int> const& pattern);
  static int decodeDigit(std::vector<int>& counters);

  void append(char* s, char c);
public:
  Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);
  ITFReader();
  ~ITFReader();
};

}
}

#endif

// file: zxing/oned/MultiFormatOneDReader.h

#ifndef __MULTI_FORMAT_ONED_READER_H__
// #define __MULTI_FORMAT_ONED_READER_H__
/*
 *  MultiFormatOneDReader.h
 *  ZXing
 *
  *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/OneDReader.h>

namespace zxing {
  namespace oned {
    class MultiFormatOneDReader : public OneDReader {

    private:
      std::vector<Ref<OneDReader> > readers;
    public:
      MultiFormatOneDReader(DecodeHints hints);

      Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);
    };
  }
}

#endif

// file: zxing/oned/MultiFormatUPCEANReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __MULTI_FORMAT_UPC_EAN_READER_H__
// #define __MULTI_FORMAT_UPC_EAN_READER_H__
/*
 *  MultiFormatUPCEANReader.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/OneDReader.h>

namespace zxing {
namespace oned {

class UPCEANReader;

class MultiFormatUPCEANReader : public OneDReader {
private:
    std::vector< Ref<UPCEANReader> > readers;
public:
    MultiFormatUPCEANReader(DecodeHints hints);
    Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);
};

}
}

#endif

// file: zxing/oned/OneDResultPoint.h

#ifndef __ONED_RESULT_POINT_H__
// #define __ONED_RESULT_POINT_H__
/*
 *  OneDResultPoint.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
// #include <zxing/ResultPoint.h>
// #include <cmath>

namespace zxing {
	namespace oned {

		class OneDResultPoint : public ResultPoint {

		public:
			OneDResultPoint(float posX, float posY);
		};
	}
}

#endif

// file: zxing/oned/UPCAReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __UPCA_READER_H__
// #define __UPCA_READER_H__
/*
 *  UPCAReader.h
 *  ZXing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/EAN13Reader.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace oned {

class UPCAReader : public UPCEANReader {

private:
  EAN13Reader ean13Reader;
  static Ref<Result> maybeReturnResult(Ref<Result> result);

public:
  UPCAReader();

  int decodeMiddle(Ref<BitArray> row, Range const& startRange, std::string& resultString);

  Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row);
  Ref<Result> decodeRow(int rowNumber, Ref<BitArray> row, Range const& startGuardRange);
  Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints);

  BarcodeFormat getBarcodeFormat();
};

}
}

#endif

// file: zxing/oned/UPCEReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __UPC_E_READER_H__
// #define __UPC_E_READER_H__

/*
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/oned/UPCEANReader.h>
// #include <zxing/Result.h>

namespace zxing {
namespace oned {

class UPCEReader : public UPCEANReader {
private:
  std::vector<int> decodeMiddleCounters;
  static bool determineNumSysAndCheckDigit(std::string& resultString, int lgPatternFound);

protected:
  Range decodeEnd(Ref<BitArray> row, int endStart);
  bool checkChecksum(Ref<String> const& s);
public:
  UPCEReader();

  int decodeMiddle(Ref<BitArray> row, Range const& startRange, std::string& resultString);
  static Ref<String> convertUPCEtoUPCA(Ref<String> const& upce);

  BarcodeFormat getBarcodeFormat();
};

}
}

#endif

// file: zxing/qrcode/ErrorCorrectionLevel.h

#ifndef __ERROR_CORRECTION_LEVEL_H__
// #define __ERROR_CORRECTION_LEVEL_H__

/*
 *  ErrorCorrectionLevel.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>

namespace zxing {
namespace qrcode {

class ErrorCorrectionLevel {
private:
  int ordinal_;
  int bits_;
  std::string name_;
  ErrorCorrectionLevel(int inOrdinal, int bits, char const* name);
  static ErrorCorrectionLevel *FOR_BITS[];
  static int N_LEVELS;
public:
  static ErrorCorrectionLevel L;
  static ErrorCorrectionLevel M;
  static ErrorCorrectionLevel Q;
  static ErrorCorrectionLevel H;

  int ordinal() const;
  int bits() const;
  std::string const& name() const;
  operator std::string const& () const;

  static ErrorCorrectionLevel& forBits(int bits);
};
}
}

#endif // __ERROR_CORRECTION_LEVEL_H__

// file: zxing/qrcode/FormatInformation.h

#ifndef __FORMAT_INFORMATION_H__
// #define __FORMAT_INFORMATION_H__

/*
 *  FormatInformation.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/qrcode/ErrorCorrectionLevel.h>
// #include <zxing/common/Counted.h>
// #include <iostream>

namespace zxing {
namespace qrcode {

class FormatInformation : public Counted {
private:
  static int FORMAT_INFO_MASK_QR;
  static int FORMAT_INFO_DECODE_LOOKUP[][2];
  static int N_FORMAT_INFO_DECODE_LOOKUPS;
  static int BITS_SET_IN_HALF_BYTE[];

  ErrorCorrectionLevel &errorCorrectionLevel_;
  char dataMask_;

  FormatInformation(int formatInfo);

public:
  static int numBitsDiffering(int a, int b);
  static Ref<FormatInformation> decodeFormatInformation(int maskedFormatInfo1, int maskedFormatInfo2);
  static Ref<FormatInformation> doDecodeFormatInformation(int maskedFormatInfo1, int maskedFormatInfo2);
  ErrorCorrectionLevel &getErrorCorrectionLevel();
  char getDataMask();
  friend bool operator==(const FormatInformation &a, const FormatInformation &b);
  friend std::ostream& operator<<(std::ostream& out, const FormatInformation& fi);
};
}
}

#endif // __FORMAT_INFORMATION_H__

// file: zxing/qrcode/decoder/Decoder.h

#ifndef __DECODER_H__
// #define __DECODER_H__

/*
 *  Decoder.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/reedsolomon/ReedSolomonDecoder.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/DecoderResult.h>
// #include <zxing/common/BitMatrix.h>

namespace zxing {
    namespace qrcode {

        class Decoder {
        private:
            ReedSolomonDecoder rsDecoder_;

            void correctErrors(ArrayRef<char> bytes, int numDataCodewords);

        public:
            Decoder();
            Ref<DecoderResult> decode(Ref<BitMatrix> bits);
        };

    }
}

#endif // __DECODER_H__

// file: zxing/qrcode/QRCodeReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __QR_CODE_READER_H__
// #define __QR_CODE_READER_H__

/*
 *  QRCodeReader.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Reader.h>
// #include <zxing/qrcode/decoder/Decoder.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace qrcode {

class QRCodeReader : public Reader {
 private:
  Decoder decoder_;

 protected:
  Decoder& getDecoder();

 public:
  QRCodeReader();
  virtual ~QRCodeReader();

  Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints);
};

}
}

#endif // __QR_CODE_READER_H__

// file: zxing/qrcode/Version.h

#ifndef __VERSION_H__
// #define __VERSION_H__

/*
 *  Version.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/qrcode/ErrorCorrectionLevel.h>
// #include <zxing/ReaderException.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Counted.h>
// #include <vector>

namespace zxing {
namespace qrcode {

class ECB {
private:
  int count_;
  int dataCodewords_;
public:
  ECB(int count, int dataCodewords);
  int getCount();
  int getDataCodewords();
};

class ECBlocks {
private:
  int ecCodewords_;
  std::vector<ECB*> ecBlocks_;
public:
  ECBlocks(int ecCodewords, ECB *ecBlocks);
  ECBlocks(int ecCodewords, ECB *ecBlocks1, ECB *ecBlocks2);
  int getECCodewords();
  std::vector<ECB*>& getECBlocks();
  ~ECBlocks();
};

class Version : public Counted {

private:
  int versionNumber_;
  std::vector<int> &alignmentPatternCenters_;
  std::vector<ECBlocks*> ecBlocks_;
  int totalCodewords_;
  Version(int versionNumber, std::vector<int> *alignmentPatternCenters, ECBlocks *ecBlocks1, ECBlocks *ecBlocks2,
          ECBlocks *ecBlocks3, ECBlocks *ecBlocks4);

public:
  static unsigned int VERSION_DECODE_INFO[];
  static int N_VERSION_DECODE_INFOS;
  static std::vector<Ref<Version> > VERSIONS;

  ~Version();
  int getVersionNumber();
  std::vector<int> &getAlignmentPatternCenters();
  int getTotalCodewords();
  int getDimensionForVersion();
  ECBlocks &getECBlocksForLevel(ErrorCorrectionLevel &ecLevel);
  static Version *getProvisionalVersionForDimension(int dimension);
  static Version *getVersionForNumber(int versionNumber);
  static Version *decodeVersionInformation(unsigned int versionBits);
  Ref<BitMatrix> buildFunctionPattern();
  static int buildVersions();
};
}
}

#endif // __VERSION_H__

// file: zxing/qrcode/decoder/BitMatrixParser.h

#ifndef __BIT_MATRIX_PARSER_H__
// #define __BIT_MATRIX_PARSER_H__

/*
 *  BitMatrixParser.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/qrcode/Version.h>
// #include <zxing/qrcode/FormatInformation.h>

namespace zxing {
namespace qrcode {

class BitMatrixParser : public Counted {
private:
  Ref<BitMatrix> bitMatrix_;
  Version *parsedVersion_;
  Ref<FormatInformation> parsedFormatInfo_;

  int copyBit(size_t x, size_t y, int versionBits);

public:
  BitMatrixParser(Ref<BitMatrix> bitMatrix);
  Ref<FormatInformation> readFormatInformation();
  Version *readVersion();
  ArrayRef<char> readCodewords();

private:
  BitMatrixParser(const BitMatrixParser&);
  BitMatrixParser& operator =(const BitMatrixParser&);

};

}
}

#endif // __BIT_MATRIX_PARSER_H__

// file: zxing/qrcode/decoder/DataBlock.h

#ifndef __DATA_BLOCK_H__
// #define __DATA_BLOCK_H__

/*
 *  DataBlock.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <vector>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/qrcode/Version.h>
// #include <zxing/qrcode/ErrorCorrectionLevel.h>

namespace zxing {
namespace qrcode {

class DataBlock : public Counted {
private:
  int numDataCodewords_;
  ArrayRef<char> codewords_;

  DataBlock(int numDataCodewords, ArrayRef<char> codewords);

public:
  static std::vector<Ref<DataBlock> >
  getDataBlocks(ArrayRef<char> rawCodewords, Version *version, ErrorCorrectionLevel &ecLevel);

  int getNumDataCodewords();
  ArrayRef<char> getCodewords();
};

}
}

#endif // __DATA_BLOCK_H__

// file: zxing/qrcode/decoder/DataMask.h

#ifndef __DATA_MASK_H__
// #define __DATA_MASK_H__

/*
 *  DataMask.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Array.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/BitMatrix.h>

// #include <vector>

namespace zxing {
namespace qrcode {

class DataMask : public Counted {
private:
  static std::vector<Ref<DataMask> > DATA_MASKS;

protected:

public:
  static int buildDataMasks();
  DataMask();
  virtual ~DataMask();
  void unmaskBitMatrix(BitMatrix& matrix, size_t dimension);
  virtual bool isMasked(size_t x, size_t y) = 0;
  static DataMask& forReference(int reference);
};

}
}

#endif // __DATA_MASK_H__

// file: zxing/common/CharacterSetECI.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __CHARACTERSET_ECI__
#define __CHARACTERSET_ECI__

/*
 * Copyright 2008-2011 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <map>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace common {

class CharacterSetECI : public Counted {
private:
  static std::map<int, zxing::Ref<CharacterSetECI> > VALUE_TO_ECI;
  static std::map<std::string, zxing::Ref<CharacterSetECI> > NAME_TO_ECI;
  static const bool inited;
  static bool init_tables();

  int const* const values_;
  char const* const* const names_;

  CharacterSetECI(int const* values, char const* const* names);

  static void addCharacterSet(int const* value, char const* const* encodingNames);

public:
  char const* name() const;
  int getValue() const;

  static CharacterSetECI* getCharacterSetECIByValue(int value);
  static CharacterSetECI* getCharacterSetECIByName(std::string const& name);
};

}
}

#endif

// file: zxing/qrcode/decoder/DecodedBitStreamParser.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __DECODED_BIT_STREAM_PARSER_H__
// #define __DECODED_BIT_STREAM_PARSER_H__

/*
 *  DecodedBitStreamParser.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <string>
// #include <sstream>
// #include <map>
// #include <zxing/qrcode/decoder/Mode.h>
// #include <zxing/common/BitSource.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/DecoderResult.h>
// #include <zxing/common/CharacterSetECI.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace qrcode {

class DecodedBitStreamParser {
public:
  typedef std::map<DecodeHintType, std::string> Hashtable;

private:
  static char const ALPHANUMERIC_CHARS[];
  static char toAlphaNumericChar(size_t value);

  static void decodeHanziSegment(Ref<BitSource> bits, std::string &result, int count);
  static void decodeKanjiSegment(Ref<BitSource> bits, std::string &result, int count);
  static void decodeByteSegment(Ref<BitSource> bits, std::string &result, int count);
  static void decodeByteSegment(Ref<BitSource> bits_,
                                std::string& result,
                                int count,
                                zxing::common::CharacterSetECI* currentCharacterSetECI,
                                ArrayRef< ArrayRef<char> >& byteSegments,
                                Hashtable const& hints);
  static void decodeAlphanumericSegment(Ref<BitSource> bits, std::string &result, int count, bool fc1InEffect);
  static void decodeNumericSegment(Ref<BitSource> bits, std::string &result, int count);

  static void append(std::string &ost, const char *bufIn, size_t nIn, const char *src);
  static void append(std::string &ost, std::string const& in, const char *src);

public:
  static Ref<DecoderResult> decode(ArrayRef<char> bytes,
                                   Version *version,
                                   ErrorCorrectionLevel const& ecLevel,
                                   Hashtable const& hints);
};

}
}

#endif // __DECODED_BIT_STREAM_PARSER_H__

// file: zxing/qrcode/decoder/Mode.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __MODE_H__
// #define __MODE_H__

/*
 *  Mode.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/qrcode/Version.h>

namespace zxing {
namespace qrcode {

class Mode {
private:
  int characterCountBitsForVersions0To9_;
  int characterCountBitsForVersions10To26_;
  int characterCountBitsForVersions27AndHigher_;
  std::string name_;

  Mode(int cbv0_9, int cbv10_26, int cbv27, int bits, char const* name);

public:
  static Mode TERMINATOR;
  static Mode NUMERIC;
  static Mode ALPHANUMERIC;
  static Mode STRUCTURED_APPEND;
  static Mode BYTE;
  static Mode ECI;
  static Mode KANJI;
  static Mode FNC1_FIRST_POSITION;
  static Mode FNC1_SECOND_POSITION;
  static Mode HANZI;

  static Mode& forBits(int bits);
  int getCharacterCountBits(Version *version);
};
}
}

#endif // __MODE_H__

// file: zxing/qrcode/detector/AlignmentPattern.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __ALIGNMENT_PATTERN_H__
// #define __ALIGNMENT_PATTERN_H__

/*
 *  AlignmentPattern.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ResultPoint.h>
// #include <cmath>

namespace zxing {
	namespace qrcode {

		class AlignmentPattern : public ResultPoint {
		private:
			float estimatedModuleSize_;

		public:
			AlignmentPattern(float posX, float posY, float estimatedModuleSize);
			bool aboutEquals(float moduleSize, float i, float j) const;
      Ref<AlignmentPattern> combineEstimate(float i, float j,
                                            float newModuleSize) const;
		};

	}
}

#endif // __ALIGNMENT_PATTERN_H__

// file: zxing/qrcode/detector/AlignmentPatternFinder.h

#ifndef __ALIGNMENT_PATTERN_FINDER_H__
// #define __ALIGNMENT_PATTERN_FINDER_H__

/*
 *  AlignmentPatternFinder.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include "AlignmentPattern.h"
// #include <zxing/common/Counted.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/ResultPointCallback.h>
// #include <vector>

namespace zxing {
namespace qrcode {

class AlignmentPatternFinder : public Counted {
private:
  static int CENTER_QUORUM;
  static int MIN_SKIP;
  static int MAX_MODULES;

  Ref<BitMatrix> image_;
  std::vector<AlignmentPattern *> *possibleCenters_;
  int startX_;
  int startY_;
  int width_;
  int height_;
  float moduleSize_;

  static float centerFromEnd(std::vector<int> &stateCount, int end);
  bool foundPatternCross(std::vector<int> &stateCount);

  float crossCheckVertical(int startI, int centerJ, int maxCount, int originalStateCountTotal);

  Ref<AlignmentPattern> handlePossibleCenter(std::vector<int> &stateCount, int i, int j);

public:
  AlignmentPatternFinder(Ref<BitMatrix> image, int startX, int startY, int width, int height,
                         float moduleSize, Ref<ResultPointCallback>const& callback);
  ~AlignmentPatternFinder();
  Ref<AlignmentPattern> find();

private:
  AlignmentPatternFinder(const AlignmentPatternFinder&);
  AlignmentPatternFinder& operator =(const AlignmentPatternFinder&);

  Ref<ResultPointCallback> callback_;
};
}
}

#endif // __ALIGNMENT_PATTERN_FINDER_H__

// file: zxing/qrcode/detector/FinderPattern.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __FINDER_PATTERN_H__
// #define __FINDER_PATTERN_H__

/*
 *  FinderPattern.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ResultPoint.h>
// #include <cmath>

namespace zxing {
    namespace qrcode {

        class FinderPattern : public ResultPoint {
        private:
            float estimatedModuleSize_;
            int count_;

            FinderPattern(float posX, float posY, float estimatedModuleSize, int count);

        public:
            FinderPattern(float posX, float posY, float estimatedModuleSize);
            int getCount() const;
            float getEstimatedModuleSize() const;
            void incrementCount();
            bool aboutEquals(float moduleSize, float i, float j) const;
            Ref<FinderPattern> combineEstimate(float i, float j, float newModuleSize) const;
        };
    }
}

#endif // __FINDER_PATTERN_H__

// file: zxing/qrcode/detector/FinderPatternInfo.h

#ifndef __FINDER_PATTERN_INFO_H__
// #define __FINDER_PATTERN_INFO_H__

/*
 *  FinderPatternInfo.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/qrcode/detector/FinderPattern.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <vector>

namespace zxing {
    namespace qrcode {

        class FinderPatternInfo : public Counted {
        private:
            Ref<FinderPattern> bottomLeft_;
            Ref<FinderPattern> topLeft_;
            Ref<FinderPattern> topRight_;

        public:
            FinderPatternInfo(std::vector<Ref<FinderPattern> > patternCenters);

            Ref<FinderPattern> getBottomLeft();
            Ref<FinderPattern> getTopLeft();
            Ref<FinderPattern> getTopRight();
        };
    }
}

#endif // __FINDER_PATTERN_INFO_H__

// file: zxing/qrcode/detector/Detector.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __DETECTOR_H__
// #define __DETECTOR_H__

/*
 *  Detector.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/DetectorResult.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/qrcode/detector/AlignmentPattern.h>
// #include <zxing/common/PerspectiveTransform.h>
// #include <zxing/ResultPointCallback.h>
// #include <zxing/qrcode/detector/FinderPatternInfo.h>

namespace zxing {

class DecodeHints;

namespace qrcode {

class Detector : public Counted {
private:
  Ref<BitMatrix> image_;
  Ref<ResultPointCallback> callback_;

protected:
  Ref<BitMatrix> getImage() const;
  Ref<ResultPointCallback> getResultPointCallback() const;

  static Ref<BitMatrix> sampleGrid(Ref<BitMatrix> image, int dimension, Ref<PerspectiveTransform>);
  static int computeDimension(Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight, Ref<ResultPoint> bottomLeft,
                              float moduleSize);
  float calculateModuleSize(Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight, Ref<ResultPoint> bottomLeft);
  float calculateModuleSizeOneWay(Ref<ResultPoint> pattern, Ref<ResultPoint> otherPattern);
  float sizeOfBlackWhiteBlackRunBothWays(int fromX, int fromY, int toX, int toY);
  float sizeOfBlackWhiteBlackRun(int fromX, int fromY, int toX, int toY);
  Ref<AlignmentPattern> findAlignmentInRegion(float overallEstModuleSize, int estAlignmentX, int estAlignmentY,
      float allowanceFactor);
  Ref<DetectorResult> processFinderPatternInfo(Ref<FinderPatternInfo> info);
public:
  virtual Ref<PerspectiveTransform> createTransform(Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight, Ref <
      ResultPoint > bottomLeft, Ref<ResultPoint> alignmentPattern, int dimension);

  Detector(Ref<BitMatrix> image);
  Ref<DetectorResult> detect(DecodeHints const& hints);


};
}
}

#endif // __DETECTOR_H__

// file: zxing/qrcode/detector/FinderPatternFinder.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __FINDER_PATTERN_FINDER_H__
// #define __FINDER_PATTERN_FINDER_H__

/*
 *  FinderPatternFinder.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/qrcode/detector/FinderPattern.h>
// #include <zxing/qrcode/detector/FinderPatternInfo.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/ResultPointCallback.h>
// #include <vector>

namespace zxing {

class DecodeHints;

namespace qrcode {

class FinderPatternFinder {
private:
  static int CENTER_QUORUM;

protected:
  static int MIN_SKIP;
  static int MAX_MODULES;

  Ref<BitMatrix> image_;
  std::vector<Ref<FinderPattern> > possibleCenters_;
  bool hasSkipped_;

  Ref<ResultPointCallback> callback_;

  /** stateCount must be int[5] */
  static float centerFromEnd(int* stateCount, int end);
  static bool foundPatternCross(int* stateCount);

  float crossCheckVertical(size_t startI, size_t centerJ, int maxCount, int originalStateCountTotal);
  float crossCheckHorizontal(size_t startJ, size_t centerI, int maxCount, int originalStateCountTotal);

  /** stateCount must be int[5] */
  bool handlePossibleCenter(int* stateCount, size_t i, size_t j);
  int findRowSkip();
  bool haveMultiplyConfirmedCenters();
  std::vector<Ref<FinderPattern> > selectBestPatterns();
  static std::vector<Ref<FinderPattern> > orderBestPatterns(std::vector<Ref<FinderPattern> > patterns);

  Ref<BitMatrix> getImage();
  std::vector<Ref<FinderPattern> >& getPossibleCenters();

public:
  static float distance(Ref<ResultPoint> p1, Ref<ResultPoint> p2);
  FinderPatternFinder(Ref<BitMatrix> image, Ref<ResultPointCallback>const&);
  Ref<FinderPatternInfo> find(DecodeHints const& hints);
};
}
}

#endif // __FINDER_PATTERN_FINDER_H__

// file: zxing/FormatException.h

#ifndef __FORMAT_EXCEPTION_H__
// #define __FORMAT_EXCEPTION_H__

/*
 *  FormatException.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>

namespace zxing {

class FormatException : public ReaderException {
public:
  FormatException();
  FormatException(const char *msg);
  ~FormatException() throw();

  static FormatException const& getFormatInstance();
};

}
#endif // __FORMAT_EXCEPTION_H__

// file: zxing/ChecksumException.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __CHECKSUM_EXCEPTION_H__
// #define __CHECKSUM_EXCEPTION_H__

/*
 * Copyright 20011 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>

namespace zxing {
  class ChecksumException : public ReaderException {
    typedef ReaderException Base;
  public:
    ChecksumException() throw();
    ChecksumException(const char *msg) throw();
    ~ChecksumException() throw();
  };
}

#endif // __CHECKSUM_EXCEPTION_H__

// file: zxing/NotFoundException.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __NOT_FOUND_EXCEPTION_H__
// #define __NOT_FOUND_EXCEPTION_H__

/*
 * Copyright 20011 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>

namespace zxing {

class NotFoundException : public ReaderException {
public:
  NotFoundException() throw() {}
  NotFoundException(const char *msg) throw() : ReaderException(msg) {}
  ~NotFoundException() throw() {}
};

}

#endif // __NOT_FOUND_EXCEPTION_H__

// file: zxing/IllegalStateException.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __ILLEGAL_STATE_EXCEPTION_H__
// #define __ILLEGAL_STATE_EXCEPTION_H__

/*
 * Copyright 20011 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may illegal use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>

namespace zxing {

class IllegalStateException : public ReaderException {
public:
  IllegalStateException() throw() {}
  IllegalStateException(const char *msg) throw() : ReaderException(msg) {}
  ~IllegalStateException() throw() {}
};

}

#endif // __ILLEGAL_STATE_EXCEPTION_H__

// file: zxing/InvertedLuminanceSource.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __INVERTEDLUMINANCESOURCE_H__
// #define __INVERTEDLUMINANCESOURCE_H__
/*
 *  Copyright 2013 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ZXing.h>
// #include <zxing/LuminanceSource.h>

namespace zxing {

class InvertedLuminanceSource : public LuminanceSource {
private:
  typedef LuminanceSource Super;
  const Ref<LuminanceSource> delegate;

public:
  InvertedLuminanceSource(Ref<LuminanceSource> const&);

  ArrayRef<char> getRow(int y, ArrayRef<char> row) const;
  ArrayRef<char> getMatrix() const;

  boolean isCropSupported() const;
  Ref<LuminanceSource> crop(int left, int top, int width, int height) const;

  boolean isRotateSupported() const;

  virtual Ref<LuminanceSource> invert() const;

  Ref<LuminanceSource> rotateCounterClockwise() const;
};

}

#endif /* INVERTEDLUMINANCESOURCE_H_ */

// file: zxing/common/StringUtils.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __STRING_UTILS__
#define __STRING_UTILS__

/*
 * Copyright (C) 2010-2011 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <string>
// #include <map>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace common {

class StringUtils {
private:
  static char const* const PLATFORM_DEFAULT_ENCODING;

  StringUtils() {}

public:
  static char const* const ASCII;
  static char const* const SHIFT_JIS;
  static char const* const GB2312;
  static char const* const EUC_JP;
  static char const* const UTF8;
  static char const* const ISO88591;
  static const bool ASSUME_SHIFT_JIS;

  typedef std::map<DecodeHintType, std::string> Hashtable;

  static std::string guessEncoding(char* bytes, int length, Hashtable const& hints);
};

}
}

#endif

// file: zxing/common/detector/JavaMath.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __ZXING_COMMON_DETECTOR_MATH_H__
// #define __ZXING_COMMON_DETECTOR_MATH_H__
/*
 *  Copyright 2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <cmath>

namespace zxing {
namespace common {
namespace detector {

class Math {
 private:
  Math();
  ~Math();
 public:

  // Java standard Math.round
  static inline int round(float a) {
    return (int)std::floor(a +0.5f);
  }

};

}
}
}

#endif

// file: zxing/common/detector/MathUtils.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __ZXING_COMMON_DETECTOR_MATHUTILS_H__
// #define __ZXING_COMMON_DETECTOR_MATHUTILS_H__
/*
 *  Copyright 2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <cmath>

namespace zxing {
namespace common {
namespace detector {

class MathUtils {
 private:
  MathUtils();
  ~MathUtils();
 public:

  /**
   * Ends up being a bit faster than {@link Math#round(float)}. This merely rounds its
   * argument to the nearest int, where x.5 rounds up to x+1.
   */
  static inline int round(float d) {
    return (int) (d + 0.5f);
  }

  static inline float distance(float aX, float aY, float bX, float bY) {
    float xDiff = aX - bX;
    float yDiff = aY - bY;
    return sqrt(xDiff * xDiff + yDiff * yDiff);
  }

  static inline float distance(int aX, int aY, int bX, int bY) {
    int xDiff = aX - bX;
    int yDiff = aY - bY;
    return sqrt(float(xDiff * xDiff + yDiff * yDiff));
  }
};

}
}
}

#endif

// file: zxing/common/detector/MonochromeRectangleDetector.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __MONOCHROMERECTANGLEDETECTOR_H__
// #define __MONOCHROMERECTANGLEDETECTOR_H__

/*
 *  MonochromeRectangleDetector.h
 *  y_wmk
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010 y_wmk authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <vector>
// #include <zxing/NotFoundException.h>
// #include <zxing/ResultPoint.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Counted.h>
// #include <zxing/ResultPoint.h>

namespace zxing {

struct TwoInts: public Counted {
  int start;
  int end;
};

class MonochromeRectangleDetector : public Counted {
 private:
  static const int MAX_MODULES = 32;
  Ref<BitMatrix> image_;

 public:
  MonochromeRectangleDetector(Ref<BitMatrix> image) : image_(image) {  };

  std::vector<Ref<ResultPoint> > detect();

 private:
  Ref<ResultPoint> findCornerFromCenter(int centerX, int deltaX, int left, int right,
                                        int centerY, int deltaY, int top, int bottom, int maxWhiteRun);

  Ref<TwoInts> blackWhiteRange(int fixedDimension, int maxWhiteRun, int minDim, int maxDim,
                               bool horizontal);

  int max(int a, float b) { return (float) a > b ? a : (int) b;};
};

}

#endif // __MONOCHROMERECTANGLEDETECTOR_H__

// file: zxing/common/detector/WhiteRectangleDetector.h

#ifndef __WHITERECTANGLEDETECTOR_H__
// #define __WHITERECTANGLEDETECTOR_H__

/*
 *  WhiteRectangleDetector.h
 *
 *
 *  Created by Luiz Silva on 09/02/2010.
 *  Copyright 2010  authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <vector>
// #include <zxing/ReaderException.h>
// #include <zxing/ResultPoint.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Counted.h>
// #include <zxing/ResultPoint.h>


namespace zxing {

class WhiteRectangleDetector : public Counted {
  private:
    static int INIT_SIZE;
    static int CORR;
    Ref<BitMatrix> image_;
    int width_;
    int height_;
    int leftInit_;
    int rightInit_;
    int downInit_;
    int upInit_;

  public:
    WhiteRectangleDetector(Ref<BitMatrix> image);
    WhiteRectangleDetector(Ref<BitMatrix> image, int initSize, int x, int y);
    std::vector<Ref<ResultPoint> > detect();

  private:
    Ref<ResultPoint> getBlackPointOnSegment(int aX, int aY, int bX, int bY);
    std::vector<Ref<ResultPoint> > centerEdges(Ref<ResultPoint> y, Ref<ResultPoint> z,
                                    Ref<ResultPoint> x, Ref<ResultPoint> t);
    bool containsBlackPoint(int a, int b, int fixed, bool horizontal);
};
}

#endif

// file: zxing/aztec/AztecDetectorResult.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  AtztecDetecorResult.h
 *  zxing
 *
 *  Created by Lukas Stabe on 08/02/2012.
 *  Copyright 2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/DetectorResult.h>

#ifndef ZXingWidget_AtztecDetecorResult_h
#define ZXingWidget_AtztecDetecorResult_h

namespace zxing {
namespace aztec {

class AztecDetectorResult : public DetectorResult {
 private:
  bool compact_;
  int nbDatablocks_, nbLayers_;
 public:
  AztecDetectorResult(Ref<BitMatrix> bits,
                      ArrayRef< Ref<ResultPoint> > points,
                      bool compact,
                      int nbDatablocks,
                      int nbLayers);
  bool isCompact();
  int getNBDatablocks();
  int getNBLayers();
};

}
}

#endif

// file: zxing/aztec/decoder/Decoder.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Decoder.h
 *  zxing
 *
 *  Created by Lukas Stabe on 08/02/2012.
 *  Copyright 2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __ZXING_AZTEC_DECODER_DECODER_H__
// #define __ZXING_AZTEC_DECODER_DECODER_H__

// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Str.h>
// #include <zxing/aztec/AztecDetectorResult.h>

namespace zxing {

    class DecoderResult;

    namespace aztec {

        class Decoder : public Counted {
        private:
            enum Table {
                UPPER,
                LOWER,
                MIXED,
                DIGIT,
                PUNCT,
                BINARY
            };

            static Table getTable(char t);
            static const char* getCharacter(Table table, int code);

            int numCodewords_;
            int codewordSize_;
            Ref<AztecDetectorResult> ddata_;
            int invertedBitCount_;

            Ref<String> getEncodedData(Ref<BitArray> correctedBits);
            Ref<BitArray> correctBits(Ref<BitArray> rawbits);
            Ref<BitArray> extractBits(Ref<BitMatrix> matrix);
            static Ref<BitMatrix> removeDashedLines(Ref<BitMatrix> matrix);
            static int readCode(Ref<BitArray> rawbits, int startIndex, int length);


        public:
            Decoder();
            Ref<DecoderResult> decode(Ref<AztecDetectorResult> detectorResult);
        };

    }
}

#endif

// file: zxing/aztec/AztecReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  AztecReader.h
 *  zxing
 *
 *  Created by Lukas Stabe on 08/02/2012.
 *  Copyright 2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Reader.h>
// #include <zxing/aztec/decoder/Decoder.h>
// #include <zxing/DecodeHints.h>

#ifndef ZXingWidget_AztecReader_h
#define ZXingWidget_AztecReader_h

namespace zxing {
namespace aztec {

class AztecReader : public Reader {
 private:
  Decoder decoder_;

 protected:
  Decoder &getDecoder();

 public:
  AztecReader();
  virtual Ref<Result> decode(Ref<BinaryBitmap> image);
  virtual Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints);
  virtual ~AztecReader();
};

}
}

#endif

// file: zxing/aztec/detector/Detector.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Detector.h
 *  zxing
 *
 *  Created by Lukas Stabe on 08/02/2012.
 *  Copyright 2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __ZXING_AZTEC_DETECTOR_DETECTOR_H__
// #define __ZXING_AZTEC_DETECTOR_DETECTOR_H__

// #include <vector>

// #include <zxing/common/BitArray.h>
// #include <zxing/ResultPoint.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/DecodeHints.h>
// #include <zxing/aztec/AztecDetectorResult.h>

namespace zxing {
namespace aztec {

class Point : public Counted {
 private:
  const int x;
  const int y;

 public:
  Ref<ResultPoint> toResultPoint() {
    return Ref<ResultPoint>(new ResultPoint(float(x), float(y)));
  }

  Point(int ax, int ay) : x(ax), y(ay) {}

  int getX() const { return x; }
  int getY() const { return y; }
};

class Detector : public Counted {

 private:
  Ref<BitMatrix> image_;

  bool compact_;
  int nbLayers_;
  int nbDataBlocks_;
  int nbCenterLayers_;
  int shift_;

  void extractParameters(std::vector<Ref<Point> > bullEyeCornerPoints);
  ArrayRef< Ref<ResultPoint> > getMatrixCornerPoints(std::vector<Ref<Point> > bullEyeCornerPoints);
  static void correctParameterData(Ref<BitArray> parameterData, bool compact);
  std::vector<Ref<Point> > getBullEyeCornerPoints(Ref<Point> pCenter);
  Ref<Point> getMatrixCenter();
  Ref<BitMatrix> sampleGrid(Ref<BitMatrix> image,
                            Ref<ResultPoint> topLeft,
                            Ref<ResultPoint> bottomLeft,
                            Ref<ResultPoint> bottomRight,
                            Ref<ResultPoint> topRight);
  void getParameters(Ref<BitArray> parameterData);
  Ref<BitArray> sampleLine(Ref<Point> p1, Ref<Point> p2, int size);
  bool isWhiteOrBlackRectangle(Ref<Point> p1,
                               Ref<Point> p2,
                               Ref<Point> p3,
                               Ref<Point> p4);
  int getColor(Ref<Point> p1, Ref<Point> p2);
  Ref<Point> getFirstDifferent(Ref<Point> init, bool color, int dx, int dy);
  bool isValid(int x, int y);
  static float distance(Ref<Point> a, Ref<Point> b);

 public:
  Detector(Ref<BitMatrix> image);
  Ref<AztecDetectorResult> detect();
};

}
}

#endif

// file: zxing/multi/ByQuadrantReader.h

#ifndef __BY_QUADRANT_READER_H__
// #define __BY_QUADRANT_READER_H__

/*
 *  Copyright 2011 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Reader.h>
// #include <zxing/BinaryBitmap.h>
// #include <zxing/Result.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace multi {

class ByQuadrantReader : public Reader {
  private:
    Reader& delegate_;

  public:
    ByQuadrantReader(Reader& delegate);
    virtual ~ByQuadrantReader();
    virtual Ref<Result> decode(Ref<BinaryBitmap> image);
    virtual Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints);
};

}
}

#endif // __BY_QUADRANT_READER_H__

// file: zxing/multi/MultipleBarcodeReader.h

#ifndef __MULTIPLE_BARCODE_READER_H__
// #define __MULTIPLE_BARCODE_READER_H__

/*
 *  Copyright 2011 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Counted.h>
// #include <zxing/Result.h>
// #include <zxing/BinaryBitmap.h>
// #include <zxing/DecodeHints.h>
// #include <vector>

namespace zxing {
    namespace multi {

        class MultipleBarcodeReader : public Counted {
        protected:
            MultipleBarcodeReader() {}
        public:
            virtual std::vector<Ref<Result> > decodeMultiple(Ref<BinaryBitmap> image);
            virtual std::vector<Ref<Result> > decodeMultiple(Ref<BinaryBitmap> image, DecodeHints hints) = 0;
            virtual ~MultipleBarcodeReader();
        };

    }
}

#endif // __MULTIPLE_BARCODE_READER_H__

// file: zxing/multi/GenericMultipleBarcodeReader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __GENERIC_MULTIPLE_BARCODE_READER_H__
// #define __GENERIC_MULTIPLE_BARCODE_READER_H__

/*
 *  Copyright 2011 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/multi/MultipleBarcodeReader.h>
// #include <zxing/Reader.h>

namespace zxing {
namespace multi {

class GenericMultipleBarcodeReader : public MultipleBarcodeReader {
 private:
  static Ref<Result> translateResultPoints(Ref<Result> result,
                                           int xOffset,
                                           int yOffset);
  void doDecodeMultiple(Ref<BinaryBitmap> image,
                        DecodeHints hints,
                        std::vector<Ref<Result> >& results,
                        int xOffset,
                        int yOffset,
                        int currentDepth);
  Reader& delegate_;
  static const int MIN_DIMENSION_TO_RECUR = 100;
  static const int MAX_DEPTH = 4;

 public:
  GenericMultipleBarcodeReader(Reader& delegate);
  virtual ~GenericMultipleBarcodeReader();
  virtual std::vector<Ref<Result> > decodeMultiple(Ref<BinaryBitmap> image, DecodeHints hints);
};

}
}

#endif // __GENERIC_MULTIPLE_BARCODE_READER_H__

// file: zxing/multi/qrcode/QRCodeMultiReader.h

#ifndef __QRCODE_MULTI_READER_H__
// #define __QRCODE_MULTI_READER_H__

/*
 *  Copyright 2011 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/multi/MultipleBarcodeReader.h>
// #include <zxing/qrcode/QRCodeReader.h>

namespace zxing {
namespace multi {

class QRCodeMultiReader: public zxing::qrcode::QRCodeReader, public MultipleBarcodeReader {
  public:
    QRCodeMultiReader();
    virtual ~QRCodeMultiReader();
    virtual std::vector<Ref<Result> > decodeMultiple(Ref<BinaryBitmap> image, DecodeHints hints);
};

}
}

#endif // __QRCODE_MULTI_READER_H__

// file: zxing/multi/qrcode/detector/MultiDetector.h

#ifndef __MULTI_DETECTOR_H__
// #define __MULTI_DETECTOR_H__

/*
 *  Copyright 2011 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/qrcode/detector/Detector.h>
// #include <zxing/common/DetectorResult.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace multi {

class MultiDetector : public zxing::qrcode::Detector {
  public:
    MultiDetector(Ref<BitMatrix> image);
    virtual ~MultiDetector();
    virtual std::vector<Ref<DetectorResult> > detectMulti(DecodeHints hints);
};

}
}

#endif // __MULTI_DETECTOR_H__

// file: zxing/multi/qrcode/detector/MultiFinderPatternFinder.h

#ifndef __MULTI_FINDER_PATTERN_FINDER_H__
// #define __MULTI_FINDER_PATTERN_FINDER_H__

/*
 *  Copyright 2011 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/qrcode/detector/FinderPattern.h>
// #include <zxing/qrcode/detector/FinderPatternFinder.h>
// #include <zxing/qrcode/detector/FinderPatternInfo.h>

namespace zxing {
namespace multi {

class MultiFinderPatternFinder : zxing::qrcode::FinderPatternFinder {
  private:
    std::vector<std::vector<Ref<zxing::qrcode::FinderPattern> > > selectBestPatterns();

    static const float MAX_MODULE_COUNT_PER_EDGE;
    static const float MIN_MODULE_COUNT_PER_EDGE;
    static const float DIFF_MODSIZE_CUTOFF_PERCENT;
    static const float DIFF_MODSIZE_CUTOFF;

  public:
    MultiFinderPatternFinder(Ref<BitMatrix> image, Ref<ResultPointCallback> resultPointCallback);
    virtual ~MultiFinderPatternFinder();
    virtual std::vector<Ref<zxing::qrcode::FinderPatternInfo> > findMulti(DecodeHints const& hints);


};

}
}

#endif // __MULTI_FINDER_PATTERN_FINDER_H__

// file: zxing/pdf417/decoder/Decoder.h

#ifndef __DECOCER_PDF_H__
// #define __DECOCER_PDF_H__

/*
 *  Decoder.h
 *  zxing
 *
 *  Created by Hartmut Neubauer, 2012-05-25
 *  Copyright 2010,2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/pdf417/decoder/ec/ErrorCorrection.h>
// #include <zxing/pdf417/decoder/ec/ModulusGF.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/DecoderResult.h>
// #include <zxing/common/BitMatrix.h>


namespace zxing {
    namespace pdf417 {
        namespace decoder {

            /**
             * <p>The main class which implements PDF417 Code decoding -- as
             * opposed to locating and extracting the PDF417 Code from an image.</p>
             *
             * <p> 2012-06-27 HFN Reed-Solomon error correction activated, see class PDF417RSDecoder. </p>
             * <p> 2012-09-19 HFN Reed-Solomon error correction via ErrorCorrection/ModulusGF/ModulusPoly. </p>
             */

            class Decoder {
            private:
                static const int MAX_ERRORS;
                static const int MAX_EC_CODEWORDS;

                void correctErrors(ArrayRef<int> codewords,
                                   ArrayRef<int> erasures, int numECCodewords);
                static void verifyCodewordCount(ArrayRef<int> codewords, int numECCodewords);

            public:

                Ref<DecoderResult> decode(Ref<BitMatrix> bits, DecodeHints const &hints);
            };

        }
    }
}

#endif // __DECOCER_PDF_H__

// file: zxing/pdf417/PDF417Reader.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __PDF417_READER_H__
// #define __PDF417_READER_H__

/*
 *  PDF417Reader.h
 *  zxing
 *
 *  Copyright 2010,2012 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/Reader.h>
// #include <zxing/pdf417/decoder/Decoder.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace pdf417 {

class PDF417Reader : public Reader {
 private:
  decoder::Decoder decoder;

  static Ref<BitMatrix> extractPureBits(Ref<BitMatrix> image);
  static int moduleSize(ArrayRef<int> leftTopBlack, Ref<BitMatrix> image);
  static int findPatternStart(int x, int y, Ref<BitMatrix> image);
  static int findPatternEnd(int x, int y, Ref<BitMatrix> image);

 public:
  Ref<Result> decode(Ref<BinaryBitmap> image, DecodeHints hints);
  void reset();
};

}
}

#endif // __PDF417_READER_H__

// file: zxing/pdf417/decoder/BitMatrixParser.h

#ifndef __BIT_MATRIX_PARSER__PDF_H__
// #define __BIT_MATRIX_PARSER__PDF_H__

/*
 *  BitMatrixParser.h / PDF417
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/ReaderException.h>
// #include <zxing/FormatException.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <stdint.h>

namespace zxing {
namespace pdf417 {
namespace decoder {

class BitMatrixParser : public Counted {
private:
  static const int MAX_ROWS;
  // Maximum Codewords (Data + Error)
  static const int MAX_CW_CAPACITY;
  static const int MODULES_IN_SYMBOL;

  Ref<BitMatrix> bitMatrix_;
  int rows_; /* = 0 */
  int leftColumnECData_; /* = 0 */
  int rightColumnECData_; /* = 0 */
  /* added 2012-06-22 HFN */
  int aLeftColumnTriple_[3];
  int aRightColumnTriple_[3];
  int eraseCount_; /* = 0 */
  ArrayRef<int> erasures_;
  int ecLevel_; /* = -1 */

public:
  static const int SYMBOL_TABLE[];
  static const int SYMBOL_TABLE_LENGTH;
  static const int CODEWORD_TABLE[];

public:
  BitMatrixParser(Ref<BitMatrix> bitMatrix);
  ArrayRef<int> getErasures() const {return erasures_;}
  int getECLevel() const {return ecLevel_;}
  int getEraseCount() const {return eraseCount_;}
  ArrayRef<int> readCodewords(); /* throw(FormatException) */
  static int getCodeword(int64_t symbol, int *pi = NULL);

private:
  bool VerifyOuterColumns(int rownumber);
  static ArrayRef<int> trimArray(ArrayRef<int> array, int size);
  static int findCodewordIndex(int64_t symbol);


  int processRow(int rowNumber,
                ArrayRef<int> codewords, int next);

  int processRow(ArrayRef<int> rowCounters, int rowNumber, int rowHeight,
    ArrayRef<int> codewords, int next); /* throw(FormatException)  */
protected:
  bool IsEqual(int &a, int &b, int rownumber);
};

}
}
}

#endif // __BIT_MATRIX_PARSER__PDF_H__

// file: zxing/pdf417/decoder/DecodedBitStreamParser.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
#ifndef __DECODED_BIT_STREAM_PARSER_PD_H__
// #define __DECODED_BIT_STREAM_PARSER_PD_H__

/*
 * Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <bigint/BigInteger.hh>
// #include <zxing/common/Array.h>
// #include <zxing/common/Str.h>
// #include <zxing/common/DecoderResult.h>

namespace zxing {
namespace pdf417 {

class DecodedBitStreamParser {
 protected:
  enum Mode {
    ALPHA,
    LOWER,
    MIXED,
    PUNCT,
    ALPHA_SHIFT,
    PUNCT_SHIFT
  };

 private:

  static const int TEXT_COMPACTION_MODE_LATCH;
  static const int BYTE_COMPACTION_MODE_LATCH;
  static const int NUMERIC_COMPACTION_MODE_LATCH;
  static const int BYTE_COMPACTION_MODE_LATCH_6;
  static const int BEGIN_MACRO_PDF417_CONTROL_BLOCK;
  static const int BEGIN_MACRO_PDF417_OPTIONAL_FIELD;
  static const int MACRO_PDF417_TERMINATOR;
  static const int MODE_SHIFT_TO_BYTE_COMPACTION_MODE;
  static const int MAX_NUMERIC_CODEWORDS;

  static const int PL;
  static const int LL;
  static const int AS;
  static const int ML;
  static const int AL;
  static const int PS;
  static const int PAL;
  static const int EXP900_SIZE;

  static const char PUNCT_CHARS[];
  static const char MIXED_CHARS[];

  static ArrayRef<BigInteger> EXP900;
  static ArrayRef<BigInteger> initEXP900();

  static int textCompaction(ArrayRef<int> codewords, int codeIndex, Ref<String> result);
  static void decodeTextCompaction(ArrayRef<int> textCompactionData,
                                   ArrayRef<int> byteCompactionData,
                                   int length,
                                   Ref<String> result);
  static int byteCompaction(int mode, ArrayRef<int> codewords, int codeIndex, Ref<String> result);
  static int numericCompaction(ArrayRef<int> codewords, int codeIndex, Ref<String> result);
  static Ref<String> decodeBase900toBase10(ArrayRef<int> codewords, int count);

 public:
  DecodedBitStreamParser();
  static Ref<DecoderResult> decode(ArrayRef<int> codewords);
};

} /* namespace pdf417 */
} /* namespace zxing */

#endif // __DECODED_BIT_STREAM_PARSER_PD_H__

// file: zxing/pdf417/decoder/ec/ModulusGF.h

#ifndef __MODULUS_GF_PDF_H__
// #define __MODULUS_GF_PDF_H__
/*
 * Copyright 2012 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * 2012-09-17 HFN translation from Java into C++
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/DecoderResult.h>
// #include <zxing/common/BitMatrix.h>

namespace zxing {
    namespace pdf417 {
        namespace decoder {
            namespace ec {

                class ModulusPoly;

                /**
                 * <p>A field based on powers of a generator integer, modulo some modulus.</p>
                 *
                 * @author Sean Owen
                 * @see com.google.zxing.common.reedsolomon.GenericGF
                 */
                class ModulusGF {

                public:
                    static ModulusGF PDF417_GF;

                private:
                    ArrayRef<int> expTable_;
                    ArrayRef<int> logTable_;
                    Ref<ModulusPoly> zero_;
                    Ref<ModulusPoly> one_;
                    int modulus_;

                public:
                    ModulusGF(int modulus, int generator);
                    Ref<ModulusPoly> getZero();
                    Ref<ModulusPoly> getOne();
                    Ref<ModulusPoly> buildMonomial(int degree, int coefficient);

                    int add(int a, int b);
                    int subtract(int a, int b);
                    int exp(int a);
                    int log(int a);
                    int inverse(int a);
                    int multiply(int a, int b);
                    int getSize();

                };

            }
        }
    }
}

#endif /* __MODULUS_GF_PDF_H__ */

// file: zxing/pdf417/decoder/ec/ModulusPoly.h

#ifndef __MODULUS_GFPOLY_PDF_H__
// #define __MODULUS_GFPOLY_PDF_H__

/*
 * Copyright 2012 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * 2012-09-17 HFN translation from Java into C++
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/DecoderResult.h>
// #include <zxing/common/BitMatrix.h>

namespace zxing {
    namespace pdf417 {
        namespace decoder {
            namespace ec {

                class ModulusGF;

                /**
                 * @author Sean Owen
                 * @see com.google.zxing.common.reedsolomon.GenericGFPoly
                 */
                class ModulusPoly: public Counted {

                private:
                    ModulusGF &field_;
                    ArrayRef<int> coefficients_;
                public:
                    ModulusPoly(ModulusGF& field, ArrayRef<int> coefficients);
                    ~ModulusPoly();
                    ArrayRef<int> getCoefficients();
                    int getDegree();
                    bool isZero();
                    int getCoefficient(int degree);
                    int evaluateAt(int a);
                    Ref<ModulusPoly> add(Ref<ModulusPoly> other);
                    Ref<ModulusPoly> subtract(Ref<ModulusPoly> other);
                    Ref<ModulusPoly> multiply(Ref<ModulusPoly> other);
                    Ref<ModulusPoly> negative();
                    Ref<ModulusPoly> multiply(int scalar);
                    Ref<ModulusPoly> multiplyByMonomial(int degree, int coefficient);
                    std::vector<Ref<ModulusPoly> > divide(Ref<ModulusPoly> other);
#if 0
                    public String toString();
#endif
                };

            }
        }
    }
}

#endif /* __MODULUS_GFPOLY_PDF_H__ */

// file: zxing/pdf417/decoder/ec/ErrorCorrection.h

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

#ifndef __ERROR_CORRECTION_PDF_H__
// #define __ERROR_CORRECTION_PDF_H__
/*
 * Copyright 2012 ZXing authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * 2012-09-17 HFN translation from Java into C++
 */

// #include <zxing/common/Counted.h>
// #include <zxing/common/Array.h>
// #include <zxing/common/DecoderResult.h>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/pdf417/decoder/ec/ModulusGF.h>
// #include <zxing/pdf417/decoder/ec/ModulusPoly.h>
// #include <zxing/common/reedsolomon/ReedSolomonException.h>

namespace zxing {
namespace pdf417 {
namespace decoder {
namespace ec {


/**
 * <p>PDF417 error correction implementation.</p>
 *
 * <p>This <a href="http://en.wikipedia.org/wiki/Reed%E2%80%93Solomon_error_correction#Example">example</a>
 * is quite useful in understanding the algorithm.</p>
 *
 * @author Sean Owen
 * @see com.google.zxing.common.reedsolomon.ReedSolomonDecoder
 */
class ErrorCorrection: public Counted {

 private:
  ModulusGF &field_;

 public:
  ErrorCorrection();
  void decode(ArrayRef<int> received,
              int numECCodewords,
              ArrayRef<int> erasures);

 private:
  std::vector<Ref<ModulusPoly> > runEuclideanAlgorithm(Ref<ModulusPoly> a, Ref<ModulusPoly> b, int R);

  ArrayRef<int> findErrorLocations(Ref<ModulusPoly> errorLocator);
  ArrayRef<int> findErrorMagnitudes(Ref<ModulusPoly> errorEvaluator,
                                    Ref<ModulusPoly> errorLocator,
                                    ArrayRef<int> errorLocations);
};

}
}
}
}

#endif /* __ERROR_CORRECTION_PDF_H__ */

// file: zxing/pdf417/detector/Detector.h

#ifndef __DETECTOR_H__
// #define __DETECTOR_H__

/*
 *  Detector.h
 *  zxing
 *
 *  Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <zxing/common/Point.h>
// #include <zxing/common/DetectorResult.h>
// #include <zxing/NotFoundException.h>
// #include <zxing/BinaryBitmap.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace pdf417 {
namespace detector {

class Detector {
private:
  static const int INTEGER_MATH_SHIFT = 8;
  static const int PATTERN_MATCH_RESULT_SCALE_FACTOR = 1 << INTEGER_MATH_SHIFT;
  static const int MAX_AVG_VARIANCE;
  static const int MAX_INDIVIDUAL_VARIANCE;

  static const int START_PATTERN[];
  static const int START_PATTERN_LENGTH;
  static const int START_PATTERN_REVERSE[];
  static const int START_PATTERN_REVERSE_LENGTH;
  static const int STOP_PATTERN[];
  static const int STOP_PATTERN_LENGTH;
  static const int STOP_PATTERN_REVERSE[];
  static const int STOP_PATTERN_REVERSE_LENGTH;

  Ref<BinaryBitmap> image_;

  static ArrayRef< Ref<ResultPoint> > findVertices(Ref<BitMatrix> matrix, int rowStep);
  static ArrayRef< Ref<ResultPoint> > findVertices180(Ref<BitMatrix> matrix, int rowStep);

  static ArrayRef<int> findGuardPattern(Ref<BitMatrix> matrix,
                                        int column,
                                        int row,
                                        int width,
                                        bool whiteFirst,
                                        const int pattern[],
                                        int patternSize,
                                        ArrayRef<int>& counters);
  static int patternMatchVariance(ArrayRef<int>& counters, const int pattern[],
                                  int maxIndividualVariance);

  static void correctVertices(Ref<BitMatrix> matrix,
                              ArrayRef< Ref<ResultPoint> >& vertices,
                              bool upsideDown);
  static void findWideBarTopBottom(Ref<BitMatrix> matrix,
                                   ArrayRef< Ref<ResultPoint> >& vertices,
                                   int offsetVertice,
                                   int startWideBar,
                                   int lenWideBar,
                                   int lenPattern,
                                   int nIncrement);
  static void findCrossingPoint(ArrayRef< Ref<ResultPoint> >& vertices,
                                int idxResult,
                                int idxLineA1,int idxLineA2,
                                int idxLineB1,int idxLineB2,
                                Ref<BitMatrix>& matrix);
  static Point intersection(Line a, Line b);
  static float computeModuleWidth(ArrayRef< Ref<ResultPoint> >& vertices);
  static int computeDimension(Ref<ResultPoint> const& topLeft,
                              Ref<ResultPoint> const& topRight,
                              Ref<ResultPoint> const& bottomLeft,
                              Ref<ResultPoint> const& bottomRight,
                              float moduleWidth);
  int computeYDimension(Ref<ResultPoint> const& topLeft,
                        Ref<ResultPoint> const& topRight,
                        Ref<ResultPoint> const& bottomLeft,
                        Ref<ResultPoint> const& bottomRight,
                        float moduleWidth);

  Ref<BitMatrix> sampleLines(ArrayRef< Ref<ResultPoint> > const& vertices, int dimensionY, int dimension);

public:
  Detector(Ref<BinaryBitmap> image);
  Ref<BinaryBitmap> getImage();
  Ref<DetectorResult> detect();
  Ref<DetectorResult> detect(DecodeHints const& hints);
};

}
}
}

#endif // __DETECTOR_H__

// file: zxing/pdf417/detector/LinesSampler.h

#ifndef __LINESSAMPLER_H__
// #define __LINESSAMPLER_H__

/*
 * Copyright 2010 ZXing authors All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// #include <map>
// #include <zxing/common/BitMatrix.h>
// #include <zxing/ResultPoint.h>
// #include <zxing/common/Point.h>

namespace zxing {
namespace pdf417 {
namespace detector {

class LinesSampler {
private:
  static const int MODULES_IN_SYMBOL = 17;
  static const int BARS_IN_SYMBOL = 8;
  static const int POSSIBLE_SYMBOLS = 2787;
  static const std::vector<float> RATIOS_TABLE;
  static std::vector<float> init_ratios_table();
  static const int BARCODE_START_OFFSET = 2;

  Ref<BitMatrix> linesMatrix_;
  int symbolsPerLine_;
  int dimension_;

  static std::vector<Ref<ResultPoint> > findVertices(Ref<BitMatrix> matrix, int rowStep);
  static std::vector<Ref<ResultPoint> > findVertices180(Ref<BitMatrix> matrix, int rowStep);

  static ArrayRef<int> findGuardPattern(Ref<BitMatrix> matrix,
                                        int column,
                                        int row,
                                        int width,
                                        bool whiteFirst,
                                        const int pattern[],
                                        int patternSize,
                                        ArrayRef<int> counters);
  static int patternMatchVariance(ArrayRef<int> counters, const int pattern[],
                                  int maxIndividualVariance);

  static void correctVertices(Ref<BitMatrix> matrix,
                              std::vector<Ref<ResultPoint> > &vertices,
                              bool upsideDown);
  static void findWideBarTopBottom(Ref<BitMatrix> matrix,
                                   std::vector<Ref<ResultPoint> > &vertices,
                                   int offsetVertice,
                                   int startWideBar,
                                   int lenWideBar,
                                   int lenPattern,
                                   int nIncrement);
  static void findCrossingPoint(std::vector<Ref<ResultPoint> > &vertices,
                                int idxResult,
                                int idxLineA1,int idxLineA2,
                                int idxLineB1,int idxLineB2,
                                Ref<BitMatrix> matrix);
  static float computeModuleWidth(std::vector<Ref<ResultPoint> > &vertices);
  static int computeDimension(Ref<ResultPoint> topLeft,
                              Ref<ResultPoint> topRight,
                              Ref<ResultPoint> bottomLeft,
                              Ref<ResultPoint> bottomRight,
                              float moduleWidth);
  int computeYDimension(Ref<ResultPoint> topLeft,
                        Ref<ResultPoint> topRight,
                        Ref<ResultPoint> bottomLeft,
                        Ref<ResultPoint> bottomRight,
                        float moduleWidth);

   Ref<BitMatrix> sampleLines(std::vector<Ref<ResultPoint> > const &vertices,
                              int dimensionY,
                              int dimension);

  static void codewordsToBitMatrix(std::vector<std::vector<int> > &codewords,
                                   Ref<BitMatrix> &matrix);
  static int calculateClusterNumber(int codeword);
  static Ref<BitMatrix> sampleGrid(Ref<BitMatrix> image,
                                   int dimension);
  static void computeSymbolWidths(std::vector<float>& symbolWidths,
                                  const int symbolsPerLine, Ref<BitMatrix> linesMatrix);
  static void linesMatrixToCodewords(std::vector<std::vector<int> > &clusterNumbers,
                                     const int symbolsPerLine,
                                     const std::vector<float> &symbolWidths,
                                     Ref<BitMatrix> linesMatrix,
                                     std::vector<std::vector<int> > &codewords);
  static std::vector<std::vector<std::map<int, int> > >
      distributeVotes(const int symbolsPerLine,
                      const std::vector<std::vector<int> >& codewords,
                      const std::vector<std::vector<int> >& clusterNumbers);
  static std::vector<int>
      findMissingLines(const int symbolsPerLine,
                       std::vector<std::vector<int> > &detectedCodeWords);
  static int decodeRowCount(const int symbolsPerLine,
                            std::vector<std::vector<int> > &detectedCodeWords,
                            std::vector<int> &insertLinesAt);

  static int round(float d);
  static Point intersection(Line a, Line b);

public:
  LinesSampler(Ref<BitMatrix> linesMatrix, int dimension);
  Ref<BitMatrix> sample();
};

}
}
}

#endif // __LINESSAMPLER_H__
