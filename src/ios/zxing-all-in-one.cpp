#include "zxing-all-in-one.h"

// file: bigint/BigInteger.cc

// #include "BigInteger.hh"

void BigInteger::operator =(const BigInteger &x) {
	// Calls like a = a have no effect
	if (this == &x)
		return;
	// Copy sign
	sign = x.sign;
	// Copy the rest
	mag = x.mag;
}

BigInteger::BigInteger(const Blk *b, Index blen, Sign s) : mag(b, blen) {
	switch (s) {
	case zero:
		if (!mag.isZero())
			throw "BigInteger::BigInteger(const Blk *, Index, Sign): Cannot use a sign of zero with a nonzero magnitude";
		sign = zero;
		break;
	case positive:
	case negative:
		// If the magnitude is zero, force the sign to zero.
		sign = mag.isZero() ? zero : s;
		break;
	default:
		/* g++ seems to be optimizing out this case on the assumption
		 * that the sign is a valid member of the enumeration.  Oh well. */
		throw "BigInteger::BigInteger(const Blk *, Index, Sign): Invalid sign";
	}
}

BigInteger::BigInteger(const BigUnsigned &x, Sign s) : mag(x) {
	switch (s) {
	case zero:
		if (!mag.isZero())
			throw "BigInteger::BigInteger(const BigUnsigned &, Sign): Cannot use a sign of zero with a nonzero magnitude";
		sign = zero;
		break;
	case positive:
	case negative:
		// If the magnitude is zero, force the sign to zero.
		sign = mag.isZero() ? zero : s;
		break;
	default:
		/* g++ seems to be optimizing out this case on the assumption
		 * that the sign is a valid member of the enumeration.  Oh well. */
		throw "BigInteger::BigInteger(const BigUnsigned &, Sign): Invalid sign";
	}
}

/* CONSTRUCTION FROM PRIMITIVE INTEGERS
 * Same idea as in BigUnsigned.cc, except that negative input results in a
 * negative BigInteger instead of an exception. */

// Done longhand to let us use initialization.
BigInteger::BigInteger(unsigned long  x) : mag(x) { sign = mag.isZero() ? zero : positive; }
BigInteger::BigInteger(unsigned int   x) : mag(x) { sign = mag.isZero() ? zero : positive; }
BigInteger::BigInteger(unsigned short x) : mag(x) { sign = mag.isZero() ? zero : positive; }

// For signed input, determine the desired magnitude and sign separately.

namespace {
	template <class X, class UX>
	BigInteger::Blk magOf(X x) {
		/* UX(...) cast needed to stop short(-2^15), which negates to
		 * itself, from sign-extending in the conversion to Blk. */
		return BigInteger::Blk(x < 0 ? UX(-x) : x);
	}
	template <class X>
	BigInteger::Sign signOf(X x) {
		return (x == 0) ? BigInteger::zero
			: (x > 0) ? BigInteger::positive
			: BigInteger::negative;
	}
}

BigInteger::BigInteger(long  x) : sign(signOf(x)), mag(magOf<long , unsigned long >(x)) {}
BigInteger::BigInteger(int   x) : sign(signOf(x)), mag(magOf<int  , unsigned int  >(x)) {}
BigInteger::BigInteger(short x) : sign(signOf(x)), mag(magOf<short, unsigned short>(x)) {}

// CONVERSION TO PRIMITIVE INTEGERS

/* Reuse BigUnsigned's conversion to an unsigned primitive integer.
 * The friend is a separate function rather than
 * BigInteger::convertToUnsignedPrimitive to avoid requiring BigUnsigned to
 * declare BigInteger. */
template <class X>
inline X convertBigUnsignedToPrimitiveAccess(const BigUnsigned &a) {
	return a.convertToPrimitive<X>();
}

template <class X>
X BigInteger::convertToUnsignedPrimitive() const {
	if (sign == negative)
		throw "BigInteger::to<Primitive>: "
			"Cannot convert a negative integer to an unsigned type";
	else
		return convertBigUnsignedToPrimitiveAccess<X>(mag);
}

/* Similar to BigUnsigned::convertToPrimitive, but split into two cases for
 * nonnegative and negative numbers. */
template <class X, class UX>
X BigInteger::convertToSignedPrimitive() const {
	if (sign == zero)
		return 0;
	else if (mag.getLength() == 1) {
		// The single block might fit in an X.  Try the conversion.
		Blk b = mag.getBlock(0);
		if (sign == positive) {
			X x = X(b);
			if (x >= 0 && Blk(x) == b)
				return x;
		} else {
			X x = -X(b);
			/* UX(...) needed to avoid rejecting conversion of
			 * -2^15 to a short. */
			if (x < 0 && Blk(UX(-x)) == b)
				return x;
		}
		// Otherwise fall through.
	}
	throw "BigInteger::to<Primitive>: "
		"Value is too big to fit in the requested type";
}

unsigned long  BigInteger::toUnsignedLong () const { return convertToUnsignedPrimitive<unsigned long >       (); }
unsigned int   BigInteger::toUnsignedInt  () const { return convertToUnsignedPrimitive<unsigned int  >       (); }
unsigned short BigInteger::toUnsignedShort() const { return convertToUnsignedPrimitive<unsigned short>       (); }
long           BigInteger::toLong         () const { return convertToSignedPrimitive  <long , unsigned long> (); }
int            BigInteger::toInt          () const { return convertToSignedPrimitive  <int  , unsigned int>  (); }
short          BigInteger::toShort        () const { return convertToSignedPrimitive  <short, unsigned short>(); }

// COMPARISON
BigInteger::CmpRes BigInteger::compareTo(const BigInteger &x) const {
	// A greater sign implies a greater number
	if (sign < x.sign)
		return less;
	else if (sign > x.sign)
		return greater;
	else switch (sign) {
		// If the signs are the same...
	case zero:
		return equal; // Two zeros are equal
	case positive:
		// Compare the magnitudes
		return mag.compareTo(x.mag);
	case negative:
		// Compare the magnitudes, but return the opposite result
		return CmpRes(-mag.compareTo(x.mag));
	default:
		throw "BigInteger internal error";
	}
}

/* COPY-LESS OPERATIONS
 * These do some messing around to determine the sign of the result,
 * then call one of BigUnsigned's copy-less operations. */

// See remarks about aliased calls in BigUnsigned.cc .
#define DTRT_ALIASED(cond, op) \
	if (cond) { \
		BigInteger tmpThis; \
		tmpThis.op; \
		*this = tmpThis; \
		return; \
	}

void BigInteger::add(const BigInteger &a, const BigInteger &b) {
	DTRT_ALIASED(this == &a || this == &b, add(a, b));
	// If one argument is zero, copy the other.
	if (a.sign == zero)
		operator =(b);
	else if (b.sign == zero)
		operator =(a);
	// If the arguments have the same sign, take the
	// common sign and add their magnitudes.
	else if (a.sign == b.sign) {
		sign = a.sign;
		mag.add(a.mag, b.mag);
	} else {
		// Otherwise, their magnitudes must be compared.
		switch (a.mag.compareTo(b.mag)) {
		case equal:
			// If their magnitudes are the same, copy zero.
			mag = 0;
			sign = zero;
			break;
			// Otherwise, take the sign of the greater, and subtract
			// the lesser magnitude from the greater magnitude.
		case greater:
			sign = a.sign;
			mag.subtract(a.mag, b.mag);
			break;
		case less:
			sign = b.sign;
			mag.subtract(b.mag, a.mag);
			break;
		}
	}
}

void BigInteger::subtract(const BigInteger &a, const BigInteger &b) {
	// Notice that this routine is identical to BigInteger::add,
	// if one replaces b.sign by its opposite.
	DTRT_ALIASED(this == &a || this == &b, subtract(a, b));
	// If a is zero, copy b and flip its sign.  If b is zero, copy a.
	if (a.sign == zero) {
		mag = b.mag;
		// Take the negative of _b_'s, sign, not ours.
		// Bug pointed out by Sam Larkin on 2005.03.30.
		sign = Sign(-b.sign);
	} else if (b.sign == zero)
		operator =(a);
	// If their signs differ, take a.sign and add the magnitudes.
	else if (a.sign != b.sign) {
		sign = a.sign;
		mag.add(a.mag, b.mag);
	} else {
		// Otherwise, their magnitudes must be compared.
		switch (a.mag.compareTo(b.mag)) {
			// If their magnitudes are the same, copy zero.
		case equal:
			mag = 0;
			sign = zero;
			break;
			// If a's magnitude is greater, take a.sign and
			// subtract a from b.
		case greater:
			sign = a.sign;
			mag.subtract(a.mag, b.mag);
			break;
			// If b's magnitude is greater, take the opposite
			// of b.sign and subtract b from a.
		case less:
			sign = Sign(-b.sign);
			mag.subtract(b.mag, a.mag);
			break;
		}
	}
}

void BigInteger::multiply(const BigInteger &a, const BigInteger &b) {
	DTRT_ALIASED(this == &a || this == &b, multiply(a, b));
	// If one object is zero, copy zero and return.
	if (a.sign == zero || b.sign == zero) {
		sign = zero;
		mag = 0;
		return;
	}
	// If the signs of the arguments are the same, the result
	// is positive, otherwise it is negative.
	sign = (a.sign == b.sign) ? positive : negative;
	// Multiply the magnitudes.
	mag.multiply(a.mag, b.mag);
}

/*
 * DIVISION WITH REMAINDER
 * Please read the comments before the definition of
 * `BigUnsigned::divideWithRemainder' in `BigUnsigned.cc' for lots of
 * information you should know before reading this function.
 *
 * Following Knuth, I decree that x / y is to be
 * 0 if y==0 and floor(real-number x / y) if y!=0.
 * Then x % y shall be x - y*(integer x / y).
 *
 * Note that x = y * (x / y) + (x % y) always holds.
 * In addition, (x % y) is from 0 to y - 1 if y > 0,
 * and from -(|y| - 1) to 0 if y < 0.  (x % y) = x if y = 0.
 *
 * Examples: (q = a / b, r = a % b)
 *	a	b	q	r
 *	===	===	===	===
 *	4	3	1	1
 *	-4	3	-2	2
 *	4	-3	-2	-2
 *	-4	-3	1	-1
 */
void BigInteger::divideWithRemainder(const BigInteger &b, BigInteger &q) {
	// Defend against aliased calls;
	// same idea as in BigUnsigned::divideWithRemainder .
	if (this == &q)
		throw "BigInteger::divideWithRemainder: Cannot write quotient and remainder into the same variable";
	if (this == &b || &q == &b) {
		BigInteger tmpB(b);
		divideWithRemainder(tmpB, q);
		return;
	}

	// Division by zero gives quotient 0 and remainder *this
	if (b.sign == zero) {
		q.mag = 0;
		q.sign = zero;
		return;
	}
	// 0 / b gives quotient 0 and remainder 0
	if (sign == zero) {
		q.mag = 0;
		q.sign = zero;
		return;
	}

	// Here *this != 0, b != 0.

	// Do the operands have the same sign?
	if (sign == b.sign) {
		// Yes: easy case.  Quotient is zero or positive.
		q.sign = positive;
	} else {
		// No: harder case.  Quotient is negative.
		q.sign = negative;
		// Decrease the magnitude of the dividend by one.
		mag--;
		/*
		 * We tinker with the dividend before and with the
		 * quotient and remainder after so that the result
		 * comes out right.  To see why it works, consider the following
		 * list of examples, where A is the magnitude-decreased
		 * a, Q and R are the results of BigUnsigned division
		 * with remainder on A and |b|, and q and r are the
		 * final results we want:
		 *
		 *	a	A	b	Q	R	q	r
		 *	-3	-2	3	0	2	-1	0
		 *	-4	-3	3	1	0	-2	2
		 *	-5	-4	3	1	1	-2	1
		 *	-6	-5	3	1	2	-2	0
		 *
		 * It appears that we need a total of 3 corrections:
		 * Decrease the magnitude of a to get A.  Increase the
		 * magnitude of Q to get q (and make it negative).
		 * Find r = (b - 1) - R and give it the desired sign.
		 */
	}

	// Divide the magnitudes.
	mag.divideWithRemainder(b.mag, q.mag);

	if (sign != b.sign) {
		// More for the harder case (as described):
		// Increase the magnitude of the quotient by one.
		q.mag++;
		// Modify the remainder.
		mag.subtract(b.mag, mag);
		mag--;
	}

	// Sign of the remainder is always the sign of the divisor b.
	sign = b.sign;

	// Set signs to zero as necessary.  (Thanks David Allen!)
	if (mag.isZero())
		sign = zero;
	if (q.mag.isZero())
		q.sign = zero;

	// WHEW!!!
}

// Negation
void BigInteger::negate(const BigInteger &a) {
	DTRT_ALIASED(this == &a, negate(a));
	// Copy a's magnitude
	mag = a.mag;
	// Copy the opposite of a.sign
	sign = Sign(-a.sign);
}

// INCREMENT/DECREMENT OPERATORS

// Prefix increment
void BigInteger::operator ++() {
	if (sign == negative) {
		mag--;
		if (mag == 0)
			sign = zero;
	} else {
		mag++;
		sign = positive; // if not already
	}
}

// Postfix increment: same as prefix
void BigInteger::operator ++(int) {
	operator ++();
}

// Prefix decrement
void BigInteger::operator --() {
	if (sign == positive) {
		mag--;
		if (mag == 0)
			sign = zero;
	} else {
		mag++;
		sign = negative;
	}
}

// Postfix decrement: same as prefix
void BigInteger::operator --(int) {
	operator --();
}

// file: bigint/BigIntegerAlgorithms.cc

// #include "BigIntegerAlgorithms.hh"

BigUnsigned gcd(BigUnsigned a, BigUnsigned b) {
	BigUnsigned trash;
	// Neat in-place alternating technique.
	for (;;) {
		if (b.isZero())
			return a;
		a.divideWithRemainder(b, trash);
		if (a.isZero())
			return b;
		b.divideWithRemainder(a, trash);
	}
}

void extendedEuclidean(BigInteger m, BigInteger n,
		BigInteger &g, BigInteger &r, BigInteger &s) {
	if (&g == &r || &g == &s || &r == &s)
		throw "BigInteger extendedEuclidean: Outputs are aliased";
	BigInteger r1(1), s1(0), r2(0), s2(1), q;
	/* Invariants:
	 * r1*m(orig) + s1*n(orig) == m(current)
	 * r2*m(orig) + s2*n(orig) == n(current) */
	for (;;) {
		if (n.isZero()) {
			r = r1; s = s1; g = m;
			return;
		}
		// Subtract q times the second invariant from the first invariant.
		m.divideWithRemainder(n, q);
		r1 -= q*r2; s1 -= q*s2;

		if (m.isZero()) {
			r = r2; s = s2; g = n;
			return;
		}
		// Subtract q times the first invariant from the second invariant.
		n.divideWithRemainder(m, q);
		r2 -= q*r1; s2 -= q*s1;
	}
}

BigUnsigned modinv(const BigInteger &x, const BigUnsigned &n) {
	BigInteger g, r, s;
	extendedEuclidean(x, n, g, r, s);
	if (g == 1)
		// r*x + s*n == 1, so r*x === 1 (mod n), so r is the answer.
		return (r % n).getMagnitude(); // (r % n) will be nonnegative
	else
		throw "BigInteger modinv: x and n have a common factor";
}

BigUnsigned modexp(const BigInteger &base, const BigUnsigned &exponent,
		const BigUnsigned &modulus) {
	BigUnsigned ans = 1, base2 = (base % modulus).getMagnitude();
	BigUnsigned::Index i = exponent.bitLength();
	// For each bit of the exponent, most to least significant...
	while (i > 0) {
		i--;
		// Square.
		ans *= ans;
		ans %= modulus;
		// And multiply if the bit is a 1.
		if (exponent.getBit(i)) {
			ans *= base2;
			ans %= modulus;
		}
	}
	return ans;
}

// file: bigint/BigIntegerUtils.cc

// #include "BigIntegerUtils.hh"
// #include "BigUnsignedInABase.hh"

std::string bigUnsignedToString(const BigUnsigned &x) {
	return std::string(BigUnsignedInABase(x, 10));
}

std::string bigIntegerToString(const BigInteger &x) {
	return (x.getSign() == BigInteger::negative)
		? (std::string("-") + bigUnsignedToString(x.getMagnitude()))
		: (bigUnsignedToString(x.getMagnitude()));
}

BigUnsigned stringToBigUnsigned(const std::string &s) {
	return BigUnsigned(BigUnsignedInABase(s, 10));
}

BigInteger stringToBigInteger(const std::string &s) {
	// Recognize a sign followed by a BigUnsigned.
	return (s[0] == '-') ? BigInteger(stringToBigUnsigned(s.substr(1, s.length() - 1)), BigInteger::negative)
		: (s[0] == '+') ? BigInteger(stringToBigUnsigned(s.substr(1, s.length() - 1)))
		: BigInteger(stringToBigUnsigned(s));
}

std::ostream &operator <<(std::ostream &os, const BigUnsigned &x) {
	BigUnsignedInABase::Base base;
	long osFlags = os.flags();
	if (osFlags & os.dec)
		base = 10;
	else if (osFlags & os.hex) {
		base = 16;
		if (osFlags & os.showbase)
			os << "0x";
	} else if (osFlags & os.oct) {
		base = 8;
		if (osFlags & os.showbase)
			os << '0';
	} else
		throw "std::ostream << BigUnsigned: Could not determine the desired base from output-stream flags";
	std::string s = std::string(BigUnsignedInABase(x, base));
	os << s;
	return os;
}

std::ostream &operator <<(std::ostream &os, const BigInteger &x) {
	if (x.getSign() == BigInteger::negative)
		os << '-';
	os << x.getMagnitude();
	return os;
}

// file: bigint/BigUnsigned.cc

// #include "BigUnsigned.hh"

// Memory management definitions have moved to the bottom of NumberlikeArray.hh.

// The templates used by these constructors and converters are at the bottom of
// BigUnsigned.hh.

BigUnsigned::BigUnsigned(unsigned long  x) { initFromPrimitive      (x); }
BigUnsigned::BigUnsigned(unsigned int   x) { initFromPrimitive      (x); }
BigUnsigned::BigUnsigned(unsigned short x) { initFromPrimitive      (x); }
BigUnsigned::BigUnsigned(         long  x) { initFromSignedPrimitive(x); }
BigUnsigned::BigUnsigned(         int   x) { initFromSignedPrimitive(x); }
BigUnsigned::BigUnsigned(         short x) { initFromSignedPrimitive(x); }

unsigned long  BigUnsigned::toUnsignedLong () const { return convertToPrimitive      <unsigned long >(); }
unsigned int   BigUnsigned::toUnsignedInt  () const { return convertToPrimitive      <unsigned int  >(); }
unsigned short BigUnsigned::toUnsignedShort() const { return convertToPrimitive      <unsigned short>(); }
long           BigUnsigned::toLong         () const { return convertToSignedPrimitive<         long >(); }
int            BigUnsigned::toInt          () const { return convertToSignedPrimitive<         int  >(); }
short          BigUnsigned::toShort        () const { return convertToSignedPrimitive<         short>(); }

// BIT/BLOCK ACCESSORS

void BigUnsigned::setBlock(Index i, Blk newBlock) {
	if (newBlock == 0) {
		if (i < len) {
			blk[i] = 0;
			zapLeadingZeros();
		}
		// If i >= len, no effect.
	} else {
		if (i >= len) {
			// The nonzero block extends the number.
			allocateAndCopy(i+1);
			// Zero any added blocks that we aren't setting.
			for (Index j = len; j < i; j++)
				blk[j] = 0;
			len = i+1;
		}
		blk[i] = newBlock;
	}
}

/* Evidently the compiler wants BigUnsigned:: on the return type because, at
 * that point, it hasn't yet parsed the BigUnsigned:: on the name to get the
 * proper scope. */
BigUnsigned::Index BigUnsigned::bitLength() const {
	if (isZero())
		return 0;
	else {
		Blk leftmostBlock = getBlock(len - 1);
		Index leftmostBlockLen = 0;
		while (leftmostBlock != 0) {
			leftmostBlock >>= 1;
			leftmostBlockLen++;
		}
		return leftmostBlockLen + (len - 1) * N;
	}
}

void BigUnsigned::setBit(Index bi, bool newBit) {
	Index blockI = bi / N;
	Blk block = getBlock(blockI), mask = Blk(1) << (bi % N);
	block = newBit ? (block | mask) : (block & ~mask);
	setBlock(blockI, block);
}

// COMPARISON
BigUnsigned::CmpRes BigUnsigned::compareTo(const BigUnsigned &x) const {
	// A bigger length implies a bigger number.
	if (len < x.len)
		return less;
	else if (len > x.len)
		return greater;
	else {
		// Compare blocks one by one from left to right.
		Index i = len;
		while (i > 0) {
			i--;
			if (blk[i] == x.blk[i])
				continue;
			else if (blk[i] > x.blk[i])
				return greater;
			else
				return less;
		}
		// If no blocks differed, the numbers are equal.
		return equal;
	}
}

// COPY-LESS OPERATIONS

/*
 * On most calls to copy-less operations, it's safe to read the inputs little by
 * little and write the outputs little by little.  However, if one of the
 * inputs is coming from the same variable into which the output is to be
 * stored (an "aliased" call), we risk overwriting the input before we read it.
 * In this case, we first compute the result into a temporary BigUnsigned
 * variable and then copy it into the requested output variable *this.
 * Each put-here operation uses the DTRT_ALIASED macro (Do The Right Thing on
 * aliased calls) to generate code for this check.
 *
 * I adopted this approach on 2007.02.13 (see Assignment Operators in
 * BigUnsigned.hh).  Before then, put-here operations rejected aliased calls
 * with an exception.  I think doing the right thing is better.
 *
 * Some of the put-here operations can probably handle aliased calls safely
 * without the extra copy because (for example) they process blocks strictly
 * right-to-left.  At some point I might determine which ones don't need the
 * copy, but my reasoning would need to be verified very carefully.  For now
 * I'll leave in the copy.
 */
#define DTRT_ALIASED_UNSIGNED(cond, op) \
	if (cond) { \
		BigUnsigned tmpThis; \
		tmpThis.op; \
		*this = tmpThis; \
		return; \
	}



void BigUnsigned::add(const BigUnsigned &a, const BigUnsigned &b) {
	DTRT_ALIASED_UNSIGNED(this == &a || this == &b, add(a, b));
	// If one argument is zero, copy the other.
	if (a.len == 0) {
		operator =(b);
		return;
	} else if (b.len == 0) {
		operator =(a);
		return;
	}
	// Some variables...
	// Carries in and out of an addition stage
	bool carryIn, carryOut;
	Blk temp;
	Index i;
	// a2 points to the longer input, b2 points to the shorter
	const BigUnsigned *a2, *b2;
	if (a.len >= b.len) {
		a2 = &a;
		b2 = &b;
	} else {
		a2 = &b;
		b2 = &a;
	}
	// Set prelimiary length and make room in this BigUnsigned
	len = a2->len + 1;
	allocate(len);
	// For each block index that is present in both inputs...
	for (i = 0, carryIn = false; i < b2->len; i++) {
		// Add input blocks
		temp = a2->blk[i] + b2->blk[i];
		// If a rollover occurred, the result is less than either input.
		// This test is used many times in the BigUnsigned code.
		carryOut = (temp < a2->blk[i]);
		// If a carry was input, handle it
		if (carryIn) {
			temp++;
			carryOut |= (temp == 0);
		}
		blk[i] = temp; // Save the addition result
		carryIn = carryOut; // Pass the carry along
	}
	// If there is a carry left over, increase blocks until
	// one does not roll over.
	for (; i < a2->len && carryIn; i++) {
		temp = a2->blk[i] + 1;
		carryIn = (temp == 0);
		blk[i] = temp;
	}
	// If the carry was resolved but the larger number
	// still has blocks, copy them over.
	for (; i < a2->len; i++)
		blk[i] = a2->blk[i];
	// Set the extra block if there's still a carry, decrease length otherwise
	if (carryIn)
		blk[i] = 1;
	else
		len--;
}

void BigUnsigned::subtract(const BigUnsigned &a, const BigUnsigned &b) {
	DTRT_ALIASED_UNSIGNED(this == &a || this == &b, subtract(a, b));
	if (b.len == 0) {
		// If b is zero, copy a.
		operator =(a);
		return;
	} else if (a.len < b.len)
		// If a is shorter than b, the result is negative.
		throw "BigUnsigned::subtract: "
			"Negative result in unsigned calculation";
	// Some variables...
	bool borrowIn, borrowOut;
	Blk temp;
	Index i;
	// Set preliminary length and make room
	len = a.len;
	allocate(len);
	// For each block index that is present in both inputs...
	for (i = 0, borrowIn = false; i < b.len; i++) {
		temp = a.blk[i] - b.blk[i];
		// If a reverse rollover occurred,
		// the result is greater than the block from a.
		borrowOut = (temp > a.blk[i]);
		// Handle an incoming borrow
		if (borrowIn) {
			borrowOut |= (temp == 0);
			temp--;
		}
		blk[i] = temp; // Save the subtraction result
		borrowIn = borrowOut; // Pass the borrow along
	}
	// If there is a borrow left over, decrease blocks until
	// one does not reverse rollover.
	for (; i < a.len && borrowIn; i++) {
		borrowIn = (a.blk[i] == 0);
		blk[i] = a.blk[i] - 1;
	}
	/* If there's still a borrow, the result is negative.
	 * Throw an exception, but zero out this object so as to leave it in a
	 * predictable state. */
	if (borrowIn) {
		len = 0;
		throw "BigUnsigned::subtract: Negative result in unsigned calculation";
	} else
		// Copy over the rest of the blocks
		for (; i < a.len; i++)
			blk[i] = a.blk[i];
	// Zap leading zeros
	zapLeadingZeros();
}

/*
 * About the multiplication and division algorithms:
 *
 * I searched unsucessfully for fast C++ built-in operations like the `b_0'
 * and `c_0' Knuth describes in Section 4.3.1 of ``The Art of Computer
 * Programming'' (replace `place' by `Blk'):
 *
 *    ``b_0[:] multiplication of a one-place integer by another one-place
 *      integer, giving a two-place answer;
 *
 *    ``c_0[:] division of a two-place integer by a one-place integer,
 *      provided that the quotient is a one-place integer, and yielding
 *      also a one-place remainder.''
 *
 * I also missed his note that ``[b]y adjusting the word size, if
 * necessary, nearly all computers will have these three operations
 * available'', so I gave up on trying to use algorithms similar to his.
 * A future version of the library might include such algorithms; I
 * would welcome contributions from others for this.
 *
 * I eventually decided to use bit-shifting algorithms.  To multiply `a'
 * and `b', we zero out the result.  Then, for each `1' bit in `a', we
 * shift `b' left the appropriate amount and add it to the result.
 * Similarly, to divide `a' by `b', we shift `b' left varying amounts,
 * repeatedly trying to subtract it from `a'.  When we succeed, we note
 * the fact by setting a bit in the quotient.  While these algorithms
 * have the same O(n^2) time complexity as Knuth's, the ``constant factor''
 * is likely to be larger.
 *
 * Because I used these algorithms, which require single-block addition
 * and subtraction rather than single-block multiplication and division,
 * the innermost loops of all four routines are very similar.  Study one
 * of them and all will become clear.
 */

/*
 * This is a little inline function used by both the multiplication
 * routine and the division routine.
 *
 * `getShiftedBlock' returns the `x'th block of `num << y'.
 * `y' may be anything from 0 to N - 1, and `x' may be anything from
 * 0 to `num.len'.
 *
 * Two things contribute to this block:
 *
 * (1) The `N - y' low bits of `num.blk[x]', shifted `y' bits left.
 *
 * (2) The `y' high bits of `num.blk[x-1]', shifted `N - y' bits right.
 *
 * But we must be careful if `x == 0' or `x == num.len', in
 * which case we should use 0 instead of (2) or (1), respectively.
 *
 * If `y == 0', then (2) contributes 0, as it should.  However,
 * in some computer environments, for a reason I cannot understand,
 * `a >> b' means `a >> (b % N)'.  This means `num.blk[x-1] >> (N - y)'
 * will return `num.blk[x-1]' instead of the desired 0 when `y == 0';
 * the test `y == 0' handles this case specially.
 */
inline BigUnsigned::Blk getShiftedBlock(const BigUnsigned &num,
	BigUnsigned::Index x, unsigned int y) {
	BigUnsigned::Blk part1 = (x == 0 || y == 0) ? 0 : (num.blk[x - 1] >> (BigUnsigned::N - y));
	BigUnsigned::Blk part2 = (x == num.len) ? 0 : (num.blk[x] << y);
	return part1 | part2;
}

void BigUnsigned::multiply(const BigUnsigned &a, const BigUnsigned &b) {
	DTRT_ALIASED_UNSIGNED(this == &a || this == &b, multiply(a, b));
	// If either a or b is zero, set to zero.
	if (a.len == 0 || b.len == 0) {
		len = 0;
		return;
	}
	/*
	 * Overall method:
	 *
	 * Set this = 0.
	 * For each 1-bit of `a' (say the `i2'th bit of block `i'):
	 *    Add `b << (i blocks and i2 bits)' to *this.
	 */
	// Variables for the calculation
	Index i, j, k;
	unsigned int i2;
	Blk temp;
	bool carryIn, carryOut;
	// Set preliminary length and make room
	len = a.len + b.len;
	allocate(len);
	// Zero out this object
	for (i = 0; i < len; i++)
		blk[i] = 0;
	// For each block of the first number...
	for (i = 0; i < a.len; i++) {
		// For each 1-bit of that block...
		for (i2 = 0; i2 < N; i2++) {
			if ((a.blk[i] & (Blk(1) << i2)) == 0)
				continue;
			/*
			 * Add b to this, shifted left i blocks and i2 bits.
			 * j is the index in b, and k = i + j is the index in this.
			 *
			 * `getShiftedBlock', a short inline function defined above,
			 * is now used for the bit handling.  It replaces the more
			 * complex `bHigh' code, in which each run of the loop dealt
			 * immediately with the low bits and saved the high bits to
			 * be picked up next time.  The last run of the loop used to
			 * leave leftover high bits, which were handled separately.
			 * Instead, this loop runs an additional time with j == b.len.
			 * These changes were made on 2005.01.11.
			 */
			for (j = 0, k = i, carryIn = false; j <= b.len; j++, k++) {
				/*
				 * The body of this loop is very similar to the body of the first loop
				 * in `add', except that this loop does a `+=' instead of a `+'.
				 */
				temp = blk[k] + getShiftedBlock(b, j, i2);
				carryOut = (temp < blk[k]);
				if (carryIn) {
					temp++;
					carryOut |= (temp == 0);
				}
				blk[k] = temp;
				carryIn = carryOut;
			}
			// No more extra iteration to deal with `bHigh'.
			// Roll-over a carry as necessary.
			for (; carryIn; k++) {
				blk[k]++;
				carryIn = (blk[k] == 0);
			}
		}
	}
	// Zap possible leading zero
	if (blk[len - 1] == 0)
		len--;
}

/*
 * DIVISION WITH REMAINDER
 * This monstrous function mods *this by the given divisor b while storing the
 * quotient in the given object q; at the end, *this contains the remainder.
 * The seemingly bizarre pattern of inputs and outputs was chosen so that the
 * function copies as little as possible (since it is implemented by repeated
 * subtraction of multiples of b from *this).
 *
 * "modWithQuotient" might be a better name for this function, but I would
 * rather not change the name now.
 */
void BigUnsigned::divideWithRemainder(const BigUnsigned &b, BigUnsigned &q) {
	/* Defending against aliased calls is more complex than usual because we
	 * are writing to both *this and q.
	 *
	 * It would be silly to try to write quotient and remainder to the
	 * same variable.  Rule that out right away. */
	if (this == &q)
		throw "BigUnsigned::divideWithRemainder: Cannot write quotient and remainder into the same variable";
	/* Now *this and q are separate, so the only concern is that b might be
	 * aliased to one of them.  If so, use a temporary copy of b. */
	if (this == &b || &q == &b) {
		BigUnsigned tmpB(b);
		divideWithRemainder(tmpB, q);
		return;
	}

	/*
	 * Knuth's definition of mod (which this function uses) is somewhat
	 * different from the C++ definition of % in case of division by 0.
	 *
	 * We let a / 0 == 0 (it doesn't matter much) and a % 0 == a, no
	 * exceptions thrown.  This allows us to preserve both Knuth's demand
	 * that a mod 0 == a and the useful property that
	 * (a / b) * b + (a % b) == a.
	 */
	if (b.len == 0) {
		q.len = 0;
		return;
	}

	/*
	 * If *this.len < b.len, then *this < b, and we can be sure that b doesn't go into
	 * *this at all.  The quotient is 0 and *this is already the remainder (so leave it alone).
	 */
	if (len < b.len) {
		q.len = 0;
		return;
	}

	// At this point we know (*this).len >= b.len > 0.  (Whew!)

	/*
	 * Overall method:
	 *
	 * For each appropriate i and i2, decreasing:
	 *    Subtract (b << (i blocks and i2 bits)) from *this, storing the
	 *      result in subtractBuf.
	 *    If the subtraction succeeds with a nonnegative result:
	 *        Turn on bit i2 of block i of the quotient q.
	 *        Copy subtractBuf back into *this.
	 *    Otherwise bit i2 of block i remains off, and *this is unchanged.
	 *
	 * Eventually q will contain the entire quotient, and *this will
	 * be left with the remainder.
	 *
	 * subtractBuf[x] corresponds to blk[x], not blk[x+i], since 2005.01.11.
	 * But on a single iteration, we don't touch the i lowest blocks of blk
	 * (and don't use those of subtractBuf) because these blocks are
	 * unaffected by the subtraction: we are subtracting
	 * (b << (i blocks and i2 bits)), which ends in at least `i' zero
	 * blocks. */
	// Variables for the calculation
	Index i, j, k;
	unsigned int i2;
	Blk temp;
	bool borrowIn, borrowOut;

	/*
	 * Make sure we have an extra zero block just past the value.
	 *
	 * When we attempt a subtraction, we might shift `b' so
	 * its first block begins a few bits left of the dividend,
	 * and then we'll try to compare these extra bits with
	 * a nonexistent block to the left of the dividend.  The
	 * extra zero block ensures sensible behavior; we need
	 * an extra block in `subtractBuf' for exactly the same reason.
	 */
	Index origLen = len; // Save real length.
	/* To avoid an out-of-bounds access in case of reallocation, allocate
	 * first and then increment the logical length. */
	allocateAndCopy(len + 1);
	len++;
	blk[origLen] = 0; // Zero the added block.

	// subtractBuf holds part of the result of a subtraction; see above.
	Blk *subtractBuf = new Blk[len];

	// Set preliminary length for quotient and make room
	q.len = origLen - b.len + 1;
	q.allocate(q.len);
	// Zero out the quotient
	for (i = 0; i < q.len; i++)
		q.blk[i] = 0;

	// For each possible left-shift of b in blocks...
	i = q.len;
	while (i > 0) {
		i--;
		// For each possible left-shift of b in bits...
		// (Remember, N is the number of bits in a Blk.)
		q.blk[i] = 0;
		i2 = N;
		while (i2 > 0) {
			i2--;
			/*
			 * Subtract b, shifted left i blocks and i2 bits, from *this,
			 * and store the answer in subtractBuf.  In the for loop, `k == i + j'.
			 *
			 * Compare this to the middle section of `multiply'.  They
			 * are in many ways analogous.  See especially the discussion
			 * of `getShiftedBlock'.
			 */
			for (j = 0, k = i, borrowIn = false; j <= b.len; j++, k++) {
				temp = blk[k] - getShiftedBlock(b, j, i2);
				borrowOut = (temp > blk[k]);
				if (borrowIn) {
					borrowOut |= (temp == 0);
					temp--;
				}
				// Since 2005.01.11, indices of `subtractBuf' directly match those of `blk', so use `k'.
				subtractBuf[k] = temp;
				borrowIn = borrowOut;
			}
			// No more extra iteration to deal with `bHigh'.
			// Roll-over a borrow as necessary.
			for (; k < origLen && borrowIn; k++) {
				borrowIn = (blk[k] == 0);
				subtractBuf[k] = blk[k] - 1;
			}
			/*
			 * If the subtraction was performed successfully (!borrowIn),
			 * set bit i2 in block i of the quotient.
			 *
			 * Then, copy the portion of subtractBuf filled by the subtraction
			 * back to *this.  This portion starts with block i and ends--
			 * where?  Not necessarily at block `i + b.len'!  Well, we
			 * increased k every time we saved a block into subtractBuf, so
			 * the region of subtractBuf we copy is just [i, k).
			 */
			if (!borrowIn) {
				q.blk[i] |= (Blk(1) << i2);
				while (k > i) {
					k--;
					blk[k] = subtractBuf[k];
				}
			}
		}
	}
	// Zap possible leading zero in quotient
	if (q.blk[q.len - 1] == 0)
		q.len--;
	// Zap any/all leading zeros in remainder
	zapLeadingZeros();
	// Deallocate subtractBuf.
	// (Thanks to Brad Spencer for noticing my accidental omission of this!)
	delete [] subtractBuf;
}

/* BITWISE OPERATORS
 * These are straightforward blockwise operations except that they differ in
 * the output length and the necessity of zapLeadingZeros. */

void BigUnsigned::bitAnd(const BigUnsigned &a, const BigUnsigned &b) {
	DTRT_ALIASED_UNSIGNED(this == &a || this == &b, bitAnd(a, b));
	// The bitwise & can't be longer than either operand.
	len = (a.len >= b.len) ? b.len : a.len;
	allocate(len);
	Index i;
	for (i = 0; i < len; i++)
		blk[i] = a.blk[i] & b.blk[i];
	zapLeadingZeros();
}

void BigUnsigned::bitOr(const BigUnsigned &a, const BigUnsigned &b) {
	DTRT_ALIASED_UNSIGNED(this == &a || this == &b, bitOr(a, b));
	Index i;
	const BigUnsigned *a2, *b2;
	if (a.len >= b.len) {
		a2 = &a;
		b2 = &b;
	} else {
		a2 = &b;
		b2 = &a;
	}
	allocate(a2->len);
	for (i = 0; i < b2->len; i++)
		blk[i] = a2->blk[i] | b2->blk[i];
	for (; i < a2->len; i++)
		blk[i] = a2->blk[i];
	len = a2->len;
	// Doesn't need zapLeadingZeros.
}

void BigUnsigned::bitXor(const BigUnsigned &a, const BigUnsigned &b) {
	DTRT_ALIASED_UNSIGNED(this == &a || this == &b, bitXor(a, b));
	Index i;
	const BigUnsigned *a2, *b2;
	if (a.len >= b.len) {
		a2 = &a;
		b2 = &b;
	} else {
		a2 = &b;
		b2 = &a;
	}
	allocate(a2->len);
	for (i = 0; i < b2->len; i++)
		blk[i] = a2->blk[i] ^ b2->blk[i];
	for (; i < a2->len; i++)
		blk[i] = a2->blk[i];
	len = a2->len;
	zapLeadingZeros();
}

void BigUnsigned::bitShiftLeft(const BigUnsigned &a, int b) {
	DTRT_ALIASED_UNSIGNED(this == &a, bitShiftLeft(a, b));
	if (b < 0) {
		if (b << 1 == 0)
			throw "BigUnsigned::bitShiftLeft: "
				"Pathological shift amount not implemented";
		else {
			bitShiftRight(a, -b);
			return;
		}
	}
	Index shiftBlocks = b / N;
	unsigned int shiftBits = b % N;
	// + 1: room for high bits nudged left into another block
	len = a.len + shiftBlocks + 1;
	allocate(len);
	Index i, j;
	for (i = 0; i < shiftBlocks; i++)
		blk[i] = 0;
	for (j = 0, i = shiftBlocks; j <= a.len; j++, i++)
		blk[i] = getShiftedBlock(a, j, shiftBits);
	// Zap possible leading zero
	if (blk[len - 1] == 0)
		len--;
}

void BigUnsigned::bitShiftRight(const BigUnsigned &a, int b) {
	DTRT_ALIASED_UNSIGNED(this == &a, bitShiftRight(a, b));
	if (b < 0) {
		if (b << 1 == 0)
			throw "BigUnsigned::bitShiftRight: "
				"Pathological shift amount not implemented";
		else {
			bitShiftLeft(a, -b);
			return;
		}
	}
	// This calculation is wacky, but expressing the shift as a left bit shift
	// within each block lets us use getShiftedBlock.
	Index rightShiftBlocks = (b + N - 1) / N;
	unsigned int leftShiftBits = N * rightShiftBlocks - b;
	// Now (N * rightShiftBlocks - leftShiftBits) == b
	// and 0 <= leftShiftBits < N.
	if (rightShiftBlocks >= a.len + 1) {
		// All of a is guaranteed to be shifted off, even considering the left
		// bit shift.
		len = 0;
		return;
	}
	// Now we're allocating a positive amount.
	// + 1: room for high bits nudged left into another block
	len = a.len + 1 - rightShiftBlocks;
	allocate(len);
	Index i, j;
	for (j = rightShiftBlocks, i = 0; j <= a.len; j++, i++)
		blk[i] = getShiftedBlock(a, j, leftShiftBits);
	// Zap possible leading zero
	if (blk[len - 1] == 0)
		len--;
}

// INCREMENT/DECREMENT OPERATORS

// Prefix increment
void BigUnsigned::operator ++() {
	Index i;
	bool carry = true;
	for (i = 0; i < len && carry; i++) {
		blk[i]++;
		carry = (blk[i] == 0);
	}
	if (carry) {
		// Allocate and then increase length, as in divideWithRemainder
		allocateAndCopy(len + 1);
		len++;
		blk[i] = 1;
	}
}

// Postfix increment: same as prefix
void BigUnsigned::operator ++(int) {
	operator ++();
}

// Prefix decrement
void BigUnsigned::operator --() {
	if (len == 0)
		throw "BigUnsigned::operator --(): Cannot decrement an unsigned zero";
	Index i;
	bool borrow = true;
	for (i = 0; borrow; i++) {
		borrow = (blk[i] == 0);
		blk[i]--;
	}
	// Zap possible leading zero (there can only be one)
	if (blk[len - 1] == 0)
		len--;
}

// Postfix decrement: same as prefix
void BigUnsigned::operator --(int) {
	operator --();
}

// file: bigint/BigUnsignedInABase.cc

// #include "BigUnsignedInABase.hh"

BigUnsignedInABase::BigUnsignedInABase(const Digit *d, Index l, Base base)
	: NumberlikeArray<Digit>(d, l), base(base) {
	// Check the base
	if (base < 2)
		throw "BigUnsignedInABase::BigUnsignedInABase(const Digit *, Index, Base): The base must be at least 2";

	// Validate the digits.
	for (Index i = 0; i < l; i++)
		if (blk[i] >= base)
			throw "BigUnsignedInABase::BigUnsignedInABase(const Digit *, Index, Base): A digit is too large for the specified base";

	// Eliminate any leading zeros we may have been passed.
	zapLeadingZeros();
}

namespace {
	unsigned int bitLen(unsigned int x) {
		unsigned int len = 0;
		while (x > 0) {
			x >>= 1;
			len++;
		}
		return len;
	}
	unsigned int ceilingDiv(unsigned int a, unsigned int b) {
		return (a + b - 1) / b;
	}
}

BigUnsignedInABase::BigUnsignedInABase(const BigUnsigned &x, Base base) {
	// Check the base
	if (base < 2)
		throw "BigUnsignedInABase(BigUnsigned, Base): The base must be at least 2";
	this->base = base;

	// Get an upper bound on how much space we need
	int maxBitLenOfX = x.getLength() * BigUnsigned::N;
	int minBitsPerDigit = bitLen(base) - 1;
	int maxDigitLenOfX = ceilingDiv(maxBitLenOfX, minBitsPerDigit);
	len = maxDigitLenOfX; // Another change to comply with `staying in bounds'.
	allocate(len); // Get the space

	BigUnsigned x2(x), buBase(base);
	Index digitNum = 0;

	while (!x2.isZero()) {
		// Get last digit.  This is like `lastDigit = x2 % buBase, x2 /= buBase'.
		BigUnsigned lastDigit(x2);
		lastDigit.divideWithRemainder(buBase, x2);
		// Save the digit.
		blk[digitNum] = lastDigit.toUnsignedShort();
		// Move on.  We can't run out of room: we figured it out above.
		digitNum++;
	}

	// Save the actual length.
	len = digitNum;
}

BigUnsignedInABase::operator BigUnsigned() const {
	BigUnsigned ans(0), buBase(base), temp;
	Index digitNum = len;
	while (digitNum > 0) {
		digitNum--;
		temp.multiply(ans, buBase);
		ans.add(temp, BigUnsigned(blk[digitNum]));
	}
	return ans;
}

BigUnsignedInABase::BigUnsignedInABase(const std::string &s, Base base) {
	// Check the base.
	if (base > 36)
		throw "BigUnsignedInABase(std::string, Base): The default string conversion routines use the symbol set 0-9, A-Z and therefore support only up to base 36.  You tried a conversion with a base over 36; write your own string conversion routine.";
	// Save the base.
	// This pattern is seldom seen in C++, but the analogous ``this.'' is common in Java.
	this->base = base;

	// `s.length()' is a `size_t', while `len' is a `NumberlikeArray::Index',
	// also known as an `unsigned int'.  Some compilers warn without this cast.
	len = Index(s.length());
	allocate(len);

	Index digitNum, symbolNumInString;
	for (digitNum = 0; digitNum < len; digitNum++) {
		symbolNumInString = len - 1 - digitNum;
		char theSymbol = s[symbolNumInString];
		if (theSymbol >= '0' && theSymbol <= '9')
			blk[digitNum] = theSymbol - '0';
		else if (theSymbol >= 'A' && theSymbol <= 'Z')
			blk[digitNum] = theSymbol - 'A' + 10;
		else if (theSymbol >= 'a' && theSymbol <= 'z')
			blk[digitNum] = theSymbol - 'a' + 10;
		else
			throw "BigUnsignedInABase(std::string, Base): Bad symbol in input.  Only 0-9, A-Z, a-z are accepted.";

		if (blk[digitNum] >= base)
			throw "BigUnsignedInABase::BigUnsignedInABase(const Digit *, Index, Base): A digit is too large for the specified base";
	}
	zapLeadingZeros();
}

BigUnsignedInABase::operator std::string() const {
	if (base > 36)
		throw "BigUnsignedInABase ==> std::string: The default string conversion routines use the symbol set 0-9, A-Z and therefore support only up to base 36.  You tried a conversion with a base over 36; write your own string conversion routine.";
	if (len == 0)
		return std::string("0");
	// Some compilers don't have push_back, so use a char * buffer instead.
	char *s = new char[len + 1];
	s[len] = '\0';
	Index digitNum, symbolNumInString;
	for (symbolNumInString = 0; symbolNumInString < len; symbolNumInString++) {
		digitNum = len - 1 - symbolNumInString;
		Digit theDigit = blk[digitNum];
		if (theDigit < 10)
			s[symbolNumInString] = char('0' + theDigit);
		else
			s[symbolNumInString] = char('A' + theDigit - 10);
	}
	std::string s2(s);
	delete [] s;
	return s2;
}

// file: zxing/BarcodeFormat.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

const char* zxing::BarcodeFormat::barcodeFormatNames[] = {
  0,
  "AZTEC",
  "CODABAR",
  "CODE_39",
  "CODE_93",
  "CODE_128",
  "DATA_MATRIX",
  "EAN_8",
  "EAN_13",
  "ITF",
  "MAXICODE",
  "PDF_417",
  "QR_CODE",
  "RSS_14",
  "RSS_EXPANDED",
  "UPC_A",
  "UPC_E",
  "UPC_EAN_EXTENSION"
};

// file: zxing/Binarizer.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Binarizer.cpp
 *  zxing
 *
 *  Created by Ralf Kistner on 16/10/2009.
 *  Copyright 2008 ZXing authors All rights reserved.
 *  Modified by Lukasz Warchol on 02/02/2010.
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

namespace zxing {

	Binarizer::Binarizer(Ref<LuminanceSource> source) : source_(source) {
  }

	Binarizer::~Binarizer() {
	}

	Ref<LuminanceSource> Binarizer::getLuminanceSource() const {
		return source_;
	}

  int Binarizer::getWidth() const {
    return source_->getWidth();
  }

  int Binarizer::getHeight() const {
    return source_->getHeight();
  }

}

// file: zxing/BinaryBitmap.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/BinaryBitmap.h>

namespace zxing {
    
    BinaryBitmap::BinaryBitmap(Ref<Binarizer> binarizer) : binarizer_(binarizer) {
    }
    
    BinaryBitmap::~BinaryBitmap() {
    }
    
    Ref<BitArray> BinaryBitmap::getBlackRow(int y, Ref<BitArray> row) {
        return binarizer_->getBlackRow(y, row);
    }
    
    Ref<BitMatrix> BinaryBitmap::getBlackMatrix() {
        return binarizer_->getBlackMatrix();
    }
    
    int BinaryBitmap::getWidth() const {
        return getLuminanceSource()->getWidth();
    }
    
    int BinaryBitmap::getHeight() const {
        return getLuminanceSource()->getHeight();
    }
    
    Ref<LuminanceSource> BinaryBitmap::getLuminanceSource() const {
        return binarizer_->getLuminanceSource();
    }
    
    
    bool BinaryBitmap::isCropSupported() const {
        return getLuminanceSource()->isCropSupported();
    }
    
    Ref<BinaryBitmap> BinaryBitmap::crop(int left, int top, int width, int height) {
        return Ref<BinaryBitmap> (new BinaryBitmap(binarizer_->createBinarizer(getLuminanceSource()->crop(left, top, width, height))));
    }
    
    bool BinaryBitmap::isRotateSupported() const {
        return getLuminanceSource()->isRotateSupported();
    }
    
    Ref<BinaryBitmap> BinaryBitmap::rotateCounterClockwise() {
        return Ref<BinaryBitmap> (new BinaryBitmap(binarizer_->createBinarizer(getLuminanceSource()->rotateCounterClockwise())));
    }
}

// file: zxing/ChecksumException.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  ChecksumException.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/ChecksumException.h>

namespace zxing {
    ChecksumException::ChecksumException() throw() {}
    ChecksumException::ChecksumException(const char *msg) throw() : ReaderException(msg) {}
    ChecksumException::~ChecksumException() throw() {}
}

// file: zxing/DecodeHints.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  DecodeHintType.cpp
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

// #include <zxing/DecodeHints.h>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
    
const DecodeHintType DecodeHints::CHARACTER_SET;

const DecodeHints DecodeHints::PRODUCT_HINT(
  UPC_A_HINT |
  UPC_E_HINT |
  EAN_13_HINT |
  EAN_8_HINT |
  RSS_14_HINT
  );

const DecodeHints DecodeHints::ONED_HINT(
  CODE_39_HINT |
  CODE_93_HINT |
  CODE_128_HINT |
  ITF_HINT |
  CODABAR_HINT |
  DecodeHints::PRODUCT_HINT
  );

const DecodeHints DecodeHints::DEFAULT_HINT(
  ONED_HINT |
  QR_CODE_HINT |
  DATA_MATRIX_HINT |
  AZTEC_HINT |
  PDF_417_HINT
  );

DecodeHints::DecodeHints() {
  hints = 0;
}

DecodeHints::DecodeHints(DecodeHintType init) {
  hints = init;
}

void DecodeHints::addFormat(BarcodeFormat toadd) {
  switch (toadd) {
  case BarcodeFormat::AZTEC: hints |= AZTEC_HINT; break;
  case BarcodeFormat::CODABAR: hints |= CODABAR_HINT; break;
  case BarcodeFormat::CODE_39: hints |= CODE_39_HINT; break;
  case BarcodeFormat::CODE_93: hints |= CODE_93_HINT; break;
  case BarcodeFormat::CODE_128: hints |= CODE_128_HINT; break;
  case BarcodeFormat::DATA_MATRIX: hints |= DATA_MATRIX_HINT; break;
  case BarcodeFormat::EAN_8: hints |= EAN_8_HINT; break;
  case BarcodeFormat::EAN_13: hints |= EAN_13_HINT; break;
  case BarcodeFormat::ITF: hints |= ITF_HINT; break;
  case BarcodeFormat::MAXICODE: hints |= MAXICODE_HINT; break;
  case BarcodeFormat::PDF_417: hints |= PDF_417_HINT; break;
  case BarcodeFormat::QR_CODE: hints |= QR_CODE_HINT; break;
  case BarcodeFormat::RSS_14: hints |= RSS_14_HINT; break;
  case BarcodeFormat::RSS_EXPANDED: hints |= RSS_EXPANDED_HINT; break;
  case BarcodeFormat::UPC_A: hints |= UPC_A_HINT; break;
  case BarcodeFormat::UPC_E: hints |= UPC_E_HINT; break;
  case BarcodeFormat::UPC_EAN_EXTENSION: hints |= UPC_EAN_EXTENSION_HINT; break;
  default: throw IllegalArgumentException("Unrecognizd barcode format");
  }
}

bool DecodeHints::containsFormat(BarcodeFormat tocheck) const {
  DecodeHintType checkAgainst = 0;
  switch (tocheck) {
  case BarcodeFormat::AZTEC: checkAgainst |= AZTEC_HINT; break;
  case BarcodeFormat::CODABAR: checkAgainst |= CODABAR_HINT; break;
  case BarcodeFormat::CODE_39: checkAgainst |= CODE_39_HINT; break;
  case BarcodeFormat::CODE_93: checkAgainst |= CODE_93_HINT; break;
  case BarcodeFormat::CODE_128: checkAgainst |= CODE_128_HINT; break;
  case BarcodeFormat::DATA_MATRIX: checkAgainst |= DATA_MATRIX_HINT; break;
  case BarcodeFormat::EAN_8: checkAgainst |= EAN_8_HINT; break;
  case BarcodeFormat::EAN_13: checkAgainst |= EAN_13_HINT; break;
  case BarcodeFormat::ITF: checkAgainst |= ITF_HINT; break;
  case BarcodeFormat::MAXICODE: checkAgainst |= MAXICODE_HINT; break;
  case BarcodeFormat::PDF_417: checkAgainst |= PDF_417_HINT; break;
  case BarcodeFormat::QR_CODE: checkAgainst |= QR_CODE_HINT; break;
  case BarcodeFormat::RSS_14: checkAgainst |= RSS_14_HINT; break;
  case BarcodeFormat::RSS_EXPANDED: checkAgainst |= RSS_EXPANDED_HINT; break;
  case BarcodeFormat::UPC_A: checkAgainst |= UPC_A_HINT; break;
  case BarcodeFormat::UPC_E: checkAgainst |= UPC_E_HINT; break;
  case BarcodeFormat::UPC_EAN_EXTENSION: checkAgainst |= UPC_EAN_EXTENSION_HINT; break;
  default: throw IllegalArgumentException("Unrecognizd barcode format");
  }
  return (hints & checkAgainst) != 0;
}

void DecodeHints::setTryHarder(bool toset) {
  if (toset) {
    hints |= TRYHARDER_HINT;
  } else {
    hints &= ~TRYHARDER_HINT;
  }
}

bool DecodeHints::getTryHarder() const {
  return (hints & TRYHARDER_HINT) != 0;
}

void DecodeHints::setResultPointCallback(Ref<ResultPointCallback> const& _callback) {
  callback = _callback;
}

Ref<ResultPointCallback> DecodeHints::getResultPointCallback() const {
  return callback;
}

DecodeHints operator | (DecodeHints const& l, DecodeHints const& r) {
  DecodeHints result (l);
  result.hints |= r.hints;
  if (!result.callback) {
    result.callback = r.callback;
  }
  return result;
}
}

// file: zxing/Exception.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Exception.cpp
 *  ZXing
 *
 *  Created by Christian Brunschen on 03/06/2008.
 *  Copyright 2008-2011 ZXing authors All rights reserved.
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
// #include <zxing/Exception.h>
// #include <string.h>

namespace zxing {

void Exception::deleteMessage() {
  delete [] message;
}

char const* Exception::copy(char const* msg) {
  char* message = 0;
  if (msg) {
    unsigned long l = strlen(msg)+1;
    if (l) {
      message = new char[l];
      strcpy(message, msg);
    }
  }
  return message;
}
}

// file: zxing/FormatException.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  FormatException.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/FormatException.h>

namespace zxing {

FormatException::FormatException() {}

FormatException::FormatException(const char *msg) :
    ReaderException(msg) {
}

FormatException::~FormatException() throw() {
}

FormatException const&
FormatException::getFormatInstance() {
  static FormatException instance;
  return instance;
}

}

// file: zxing/InvertedLuminanceSource.cpp

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

// #include <zxing/ZXing.h>
// #include <zxing/InvertedLuminanceSource.h>

namespace zxing {
    
InvertedLuminanceSource::InvertedLuminanceSource(Ref<LuminanceSource> const& delegate_)
    : Super(delegate_->getWidth(), delegate_->getHeight()), delegate(delegate_) {}

ArrayRef<char> InvertedLuminanceSource::getRow(int y, ArrayRef<char> row) const {
  row = delegate->getRow(y, row);
  int width = getWidth();
  for (int i = 0; i < width; i++) {
    row[i] = (byte) (255 - (row[i] & 0xFF));
  }
  return row;
}

ArrayRef<char> InvertedLuminanceSource::getMatrix() const {
  ArrayRef<char> matrix = delegate->getMatrix();
  int length = getWidth() * getHeight();
  ArrayRef<char> invertedMatrix(length);
  for (int i = 0; i < length; i++) {
    invertedMatrix[i] = (byte) (255 - (matrix[i] & 0xFF));
  }
  return invertedMatrix;
}

zxing::boolean InvertedLuminanceSource::isCropSupported() const {
  return delegate->isCropSupported();
}

Ref<LuminanceSource> InvertedLuminanceSource::crop(int left, int top, int width, int height) const {
  return Ref<LuminanceSource>(new InvertedLuminanceSource(delegate->crop(left, top, width, height)));
}

boolean InvertedLuminanceSource::isRotateSupported() const {
  return delegate->isRotateSupported();
}

Ref<LuminanceSource> InvertedLuminanceSource::invert() const {
  return delegate;
}

Ref<LuminanceSource> InvertedLuminanceSource::rotateCounterClockwise() const {
  return Ref<LuminanceSource>(new InvertedLuminanceSource(delegate->rotateCounterClockwise()));
}
}

// file: zxing/LuminanceSource.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  LuminanceSource.cpp
 *  zxing
 *
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <sstream>
// #include <zxing/LuminanceSource.h>
// #include <zxing/InvertedLuminanceSource.h>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {

LuminanceSource::LuminanceSource(int width_, int height_) :width(width_), height(height_) {}

LuminanceSource::~LuminanceSource() {}

bool LuminanceSource::isCropSupported() const {
  return false;
}

Ref<LuminanceSource> LuminanceSource::crop(int, int, int, int) const {
  throw IllegalArgumentException("This luminance source does not support cropping.");
}

bool LuminanceSource::isRotateSupported() const {
  return false;
}

Ref<LuminanceSource> LuminanceSource::rotateCounterClockwise() const {
  throw IllegalArgumentException("This luminance source does not support rotation.");
}

LuminanceSource::operator std::string() const {
  ArrayRef<char> row;
  std::ostringstream oss;
  for (int y = 0; y < getHeight(); y++) {
    row = getRow(y, row);
    for (int x = 0; x < getWidth(); x++) {
      int luminance = row[x] & 0xFF;
      char c;
      if (luminance < 0x40) {
        c = '#';
      } else if (luminance < 0x80) {
        c = '+';
      } else if (luminance < 0xC0) {
        c = '.';
      } else {
        c = ' ';
      }
      oss << c;
    }
    oss << '\n';
  }
  return oss.str();
}

Ref<LuminanceSource> LuminanceSource::invert() const {

  // N.B.: this only works because we use counted objects with the
  // count in the object. This is _not_ how things like shared_ptr
  // work. They do not allow you to make a smart pointer from a native
  // pointer more than once. If we ever switch to (something like)
  // shared_ptr's, the luminace source is going to have keep a weak
  // pointer to itself from which it can create a strong pointer as
  // needed. And, FWIW, that has nasty semantics in the face of
  // exceptions during construction.

  return Ref<LuminanceSource>
      (new InvertedLuminanceSource(Ref<LuminanceSource>(const_cast<LuminanceSource*>(this))));
}
}

// file: zxing/MultiFormatReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/ZXing.h>
// #include <zxing/MultiFormatReader.h>
// #include <zxing/qrcode/QRCodeReader.h>
// #include <zxing/datamatrix/DataMatrixReader.h>
// #include <zxing/aztec/AztecReader.h>
// #include <zxing/pdf417/PDF417Reader.h>
// #include <zxing/oned/MultiFormatUPCEANReader.h>
// #include <zxing/oned/MultiFormatOneDReader.h>
// #include <zxing/ReaderException.h>

namespace zxing {

MultiFormatReader::MultiFormatReader() {}

Ref<Result> MultiFormatReader::decode(Ref<BinaryBitmap> image) {
  setHints(DecodeHints::DEFAULT_HINT);
  return decodeInternal(image);
}

Ref<Result> MultiFormatReader::decode(Ref<BinaryBitmap> image, DecodeHints hints) {
  setHints(hints);
  return decodeInternal(image);
}

Ref<Result> MultiFormatReader::decodeWithState(Ref<BinaryBitmap> image) {
  // Make sure to set up the default state so we don't crash
  if (readers_.size() == 0) {
    setHints(DecodeHints::DEFAULT_HINT);
  }
  return decodeInternal(image);
}

void MultiFormatReader::setHints(DecodeHints hints) {
  hints_ = hints;
  readers_.clear();
  bool tryHarder = hints.getTryHarder();

  bool addOneDReader = hints.containsFormat(BarcodeFormat::UPC_E) ||
    hints.containsFormat(BarcodeFormat::UPC_A) ||
    hints.containsFormat(BarcodeFormat::UPC_E) ||
    hints.containsFormat(BarcodeFormat::EAN_13) ||
    hints.containsFormat(BarcodeFormat::EAN_8) ||
    hints.containsFormat(BarcodeFormat::CODABAR) ||
    hints.containsFormat(BarcodeFormat::CODE_39) ||
    hints.containsFormat(BarcodeFormat::CODE_93) ||
    hints.containsFormat(BarcodeFormat::CODE_128) ||
    hints.containsFormat(BarcodeFormat::ITF) ||
    hints.containsFormat(BarcodeFormat::RSS_14) ||
    hints.containsFormat(BarcodeFormat::RSS_EXPANDED);
  if (addOneDReader && !tryHarder) {
    readers_.push_back(Ref<Reader>(new zxing::oned::MultiFormatOneDReader(hints)));
  }
  if (hints.containsFormat(BarcodeFormat::QR_CODE)) {
    readers_.push_back(Ref<Reader>(new zxing::qrcode::QRCodeReader()));
  }
  if (hints.containsFormat(BarcodeFormat::DATA_MATRIX)) {
    readers_.push_back(Ref<Reader>(new zxing::datamatrix::DataMatrixReader()));
  }
  if (hints.containsFormat(BarcodeFormat::AZTEC)) {
    readers_.push_back(Ref<Reader>(new zxing::aztec::AztecReader()));
  }
  if (hints.containsFormat(BarcodeFormat::PDF_417)) {
    readers_.push_back(Ref<Reader>(new zxing::pdf417::PDF417Reader()));
  }
  /*
  if (hints.contains(BarcodeFormat.MAXICODE)) {
    readers.add(new MaxiCodeReader());
  }
  */
  if (addOneDReader && tryHarder) {
    readers_.push_back(Ref<Reader>(new zxing::oned::MultiFormatOneDReader(hints)));
  }
  if (readers_.size() == 0) {
    if (!tryHarder) {
      readers_.push_back(Ref<Reader>(new zxing::oned::MultiFormatOneDReader(hints)));
    }
    readers_.push_back(Ref<Reader>(new zxing::qrcode::QRCodeReader()));
    readers_.push_back(Ref<Reader>(new zxing::datamatrix::DataMatrixReader()));
    readers_.push_back(Ref<Reader>(new zxing::aztec::AztecReader()));
    readers_.push_back(Ref<Reader>(new zxing::pdf417::PDF417Reader()));
    // readers.add(new MaxiCodeReader());

    if (tryHarder) {
      readers_.push_back(Ref<Reader>(new zxing::oned::MultiFormatOneDReader(hints)));
    }
  }
}

Ref<Result> MultiFormatReader::decodeInternal(Ref<BinaryBitmap> image) {
  for (unsigned int i = 0; i < readers_.size(); i++) {
    try {
      return readers_[i]->decode(image, hints_);
    } catch (ReaderException const& re) {
      (void)re;
      // continue
    }
  }
  throw ReaderException("No code detected");
}
    

MultiFormatReader::~MultiFormatReader() {}
}

// file: zxing/Reader.cpp

/*
 *  Reader.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

Reader::~Reader() { }

Ref<Result> Reader::decode(Ref<BinaryBitmap> image) {
  return decode(image, DecodeHints::DEFAULT_HINT);
}

}

// file: zxing/Result.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Result.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/Result.h>

namespace zxing {
using namespace std;

Result::Result(Ref<String> text,
               ArrayRef<char> rawBytes,
               ArrayRef< Ref<ResultPoint> > resultPoints,
               BarcodeFormat format) :
  text_(text), rawBytes_(rawBytes), resultPoints_(resultPoints), format_(format) {
}

Result::~Result() {
}

Ref<String> Result::getText() {
  return text_;
}

ArrayRef<char> Result::getRawBytes() {
  return rawBytes_;
}

ArrayRef< Ref<ResultPoint> > const& Result::getResultPoints() const {
  return resultPoints_;
}

ArrayRef< Ref<ResultPoint> >& Result::getResultPoints() {
  return resultPoints_;
}

zxing::BarcodeFormat Result::getBarcodeFormat() const {
  return format_;
}
}

// file: zxing/ResultIO.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  ResultIO.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/Result.h>

namespace zxing {
    
ostream& operator<<(ostream &out, Result& result) {
  if (result.text_ != 0) {
    out << result.text_->getText();
  } else {
    out << "[" << result.rawBytes_->size() << " bytes]";
  }
  return out;
}
}

// file: zxing/ResultPoint.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  ResultPoint.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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
// #include <zxing/common/detector/MathUtils.h>

using zxing::common::detector::MathUtils;

namespace zxing {

ResultPoint::ResultPoint() : posX_(0), posY_(0) {}

ResultPoint::ResultPoint(float x, float y) : posX_(x), posY_(y) {}

ResultPoint::ResultPoint(int x, int y) : posX_(float(x)), posY_(float(y)) {}

ResultPoint::~ResultPoint() {}

float ResultPoint::getX() const {
  return posX_;
}

float ResultPoint::getY() const {
  return posY_;
}

bool ResultPoint::equals(Ref<ResultPoint> other) {
  return posX_ == other->getX() && posY_ == other->getY();
}

/**
 * <p>Orders an array of three ResultPoints in an order [A,B,C] such that AB < AC and
 * BC < AC and the angle between BC and BA is less than 180 degrees.
 */
void ResultPoint::orderBestPatterns(std::vector<Ref<ResultPoint> > &patterns) {
    // Find distances between pattern centers
    float zeroOneDistance = distance(patterns[0]->getX(), patterns[1]->getX(),patterns[0]->getY(), patterns[1]->getY());
    float oneTwoDistance = distance(patterns[1]->getX(), patterns[2]->getX(),patterns[1]->getY(), patterns[2]->getY());
    float zeroTwoDistance = distance(patterns[0]->getX(), patterns[2]->getX(),patterns[0]->getY(), patterns[2]->getY());

    Ref<ResultPoint> pointA, pointB, pointC;
    // Assume one closest to other two is B; A and C will just be guesses at first
    if (oneTwoDistance >= zeroOneDistance && oneTwoDistance >= zeroTwoDistance) {
      pointB = patterns[0];
      pointA = patterns[1];
      pointC = patterns[2];
    } else if (zeroTwoDistance >= oneTwoDistance && zeroTwoDistance >= zeroOneDistance) {
      pointB = patterns[1];
      pointA = patterns[0];
      pointC = patterns[2];
    } else {
      pointB = patterns[2];
      pointA = patterns[0];
      pointC = patterns[1];
    }

    // Use cross product to figure out whether A and C are correct or flipped.
    // This asks whether BC x BA has a positive z component, which is the arrangement
    // we want for A, B, C. If it's negative, then we've got it flipped around and
    // should swap A and C.
    if (crossProductZ(pointA, pointB, pointC) < 0.0f) {
      Ref<ResultPoint> temp = pointA;
      pointA = pointC;
      pointC = temp;
    }

    patterns[0] = pointA;
    patterns[1] = pointB;
    patterns[2] = pointC;
}

  float ResultPoint::distance(Ref<ResultPoint> pattern1, Ref<ResultPoint> pattern2) {
  return MathUtils::distance(pattern1->posX_,
                             pattern1->posY_,
                             pattern2->posX_,
                             pattern2->posY_);
}

float ResultPoint::distance(float x1, float x2, float y1, float y2) {
  float xDiff = x1 - x2;
  float yDiff = y1 - y2;
  return (float) sqrt((double) (xDiff * xDiff + yDiff * yDiff));
}

float ResultPoint::crossProductZ(Ref<ResultPoint> pointA, Ref<ResultPoint> pointB, Ref<ResultPoint> pointC) {
  float bX = pointB->getX();
  float bY = pointB->getY();
  return ((pointC->getX() - bX) * (pointA->getY() - bY)) - ((pointC->getY() - bY) * (pointA->getX() - bX));
}
}

// file: zxing/ResultPointCallback.cpp

/*
 *  ResultPointCallback.cpp
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

// #include <zxing/ResultPointCallback.h>

namespace zxing {

ResultPointCallback::~ResultPointCallback() {}

}

// file: zxing/aztec/AztecDetectorResult.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  AtztecDetecorResult.cpp
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

// #include <zxing/aztec/AztecDetectorResult.h>

namespace zxing {
namespace aztec {
        
AztecDetectorResult::AztecDetectorResult(Ref<BitMatrix> bits,
                                         ArrayRef< Ref<ResultPoint> > points,
                                         bool compact,
                                         int nbDatablocks,
                                         int nbLayers)
  : DetectorResult(bits, points),
    compact_(compact),
    nbDatablocks_(nbDatablocks),
    nbLayers_(nbLayers) {
    }

bool AztecDetectorResult::isCompact() {
  return compact_;
}

int AztecDetectorResult::getNBDatablocks() {
  return nbDatablocks_;
}

int AztecDetectorResult::getNBLayers() {
  return nbLayers_;
}
}
}

// file: zxing/aztec/AztecReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  AztecReader.cpp
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

// #include <zxing/aztec/AztecReader.h>
// #include <zxing/aztec/detector/Detector.h>
// #include <zxing/common/DecoderResult.h>
// #include <iostream>

namespace zxing {
    namespace aztec {
        
AztecReader::AztecReader() : decoder_() {
  // nothing
}

Ref<Result> AztecReader::decode(Ref<zxing::BinaryBitmap> image) {
  Detector detector(image->getBlackMatrix());

  Ref<AztecDetectorResult> detectorResult(detector.detect());

  ArrayRef< Ref<ResultPoint> > points(detectorResult->getPoints());

  Ref<DecoderResult> decoderResult(decoder_.decode(detectorResult));

  Ref<Result> result(new Result(decoderResult->getText(),
                                decoderResult->getRawBytes(),
                                points,
                                BarcodeFormat::AZTEC));

  return result;
}

Ref<Result> AztecReader::decode(Ref<BinaryBitmap> image, DecodeHints) {
  //cout << "decoding with hints not supported for aztec" << "\n" << flush;
  return this->decode(image);
}

AztecReader::~AztecReader() {
  // nothing
}

zxing::aztec::Decoder& AztecReader::getDecoder() {
  return decoder_;
}
}
}

// file: zxing/aztec/decoder/Decoder.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Decoder.cpp
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

// #include <zxing/aztec/decoder/Decoder.h>
// #ifndef NO_ICONV
// #include <iconv.h>
// #endif
// #include <iostream>
// #include <zxing/FormatException.h>
// #include <zxing/common/reedsolomon/ReedSolomonDecoder.h>
// #include <zxing/common/reedsolomon/ReedSolomonException.h>
// #include <zxing/common/reedsolomon/GenericGF.h>
// #include <zxing/common/IllegalArgumentException.h>
// #include <zxing/common/DecoderResult.h>

namespace zxing {
namespace aztec {
        
namespace {
  void add(string& result, char character) {
#ifndef NO_ICONV
    char character2 = character & 0xff;
    char s[] =  {character2};
    char* ss = s;
    size_t sl = sizeof(s);
    char d[4];
    char* ds = d;
    size_t dl = sizeof(d);
    iconv_t ic = iconv_open("UTF-8", "ISO-8859-1");
    iconv(ic, &ss, &sl, &ds, &dl);
    iconv_close(ic);
    d[sizeof(d)-dl] = 0;
    result.append(d);
#else
    result.push_back(character);
#endif
  }

  const int NB_BITS_COMPACT[] = {
    0, 104, 240, 408, 608
  };

  const int NB_BITS[] = {
    0, 128, 288, 480, 704, 960, 1248, 1568, 1920, 2304, 2720, 3168, 3648, 4160, 4704, 5280, 5888, 6528,
    7200, 7904, 8640, 9408, 10208, 11040, 11904, 12800, 13728, 14688, 15680, 16704, 17760, 18848, 19968
  };

  const int NB_DATABLOCK_COMPACT[] = {
    0, 17, 40, 51, 76
  };

  const int NB_DATABLOCK[] = {
    0, 21, 48, 60, 88, 120, 156, 196, 240, 230, 272, 316, 364, 416, 470, 528, 588, 652, 720, 790, 864,
    940, 1020, 920, 992, 1066, 1144, 1224, 1306, 1392, 1480, 1570, 1664
  };

  const char* UPPER_TABLE[] = {
    "CTRL_PS", " ", "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P",
    "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z", "CTRL_LL", "CTRL_ML", "CTRL_DL", "CTRL_BS"
  };

  const char* LOWER_TABLE[] = {
    "CTRL_PS", " ", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p",
    "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "CTRL_US", "CTRL_ML", "CTRL_DL", "CTRL_BS"
  };

  const char* MIXED_TABLE[] = {
    "CTRL_PS", " ", "\1", "\2", "\3", "\4", "\5", "\6", "\7", "\b", "\t", "\n",
    "\13", "\f", "\r", "\33", "\34", "\35", "\36", "\37", "@", "\\", "^", "_",
    "`", "|", "~", "\177", "CTRL_LL", "CTRL_UL", "CTRL_PL", "CTRL_BS"
  };

  const char* PUNCT_TABLE[] = {
    "", "\r", "\r\n", ". ", ", ", ": ", "!", "\"", "#", "$", "%", "&", "'", "(", ")",
    "*", "+", ",", "-", ".", "/", ":", ";", "<", "=", ">", "?", "[", "]", "{", "}", "CTRL_UL"
  };

  const char* DIGIT_TABLE[] = {
    "CTRL_PS", " ", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", ",", ".", "CTRL_UL", "CTRL_US"
  };
}

Decoder::Table Decoder::getTable(char t) {
  switch (t) {
  case 'L':
    return LOWER;
  case 'P':
    return PUNCT;
  case 'M':
    return MIXED;
  case 'D':
    return DIGIT;
  case 'B':
    return BINARY;
  case 'U':
  default:
    return UPPER;
  }
}

const char* Decoder::getCharacter(zxing::aztec::Decoder::Table table, int code) {
  switch (table) {
  case UPPER:
    return UPPER_TABLE[code];
  case LOWER:
    return LOWER_TABLE[code];
  case MIXED:
    return MIXED_TABLE[code];
  case PUNCT:
    return PUNCT_TABLE[code];
  case DIGIT:
    return DIGIT_TABLE[code];
  default:
    return "";
  }
}

Decoder::Decoder() {
  // nothing
}

Ref<DecoderResult> Decoder::decode(Ref<zxing::aztec::AztecDetectorResult> detectorResult) {
  ddata_ = detectorResult;

  // std::printf("getting bits\n");

  Ref<BitMatrix> matrix = detectorResult->getBits();

  if (!ddata_->isCompact()) {
    // std::printf("removing lines\n");
    matrix = removeDashedLines(ddata_->getBits());
  }

  // std::printf("extracting bits\n");
  Ref<BitArray> rawbits = extractBits(matrix);

  // std::printf("correcting bits\n");
  Ref<BitArray> aCorrectedBits = correctBits(rawbits);

  // std::printf("decoding bits\n");
  Ref<String> result = getEncodedData(aCorrectedBits);

  // std::printf("constructing array\n");
  ArrayRef<char> arrayOut(aCorrectedBits->getSize());
  for (int i = 0; i < aCorrectedBits->count(); i++) {
    arrayOut[i] = (char)aCorrectedBits->get(i);
  }

  // std::printf("returning\n");

  return Ref<DecoderResult>(new DecoderResult(arrayOut, result));
}

Ref<String> Decoder::getEncodedData(Ref<zxing::BitArray> correctedBits) {
  int endIndex = codewordSize_ * ddata_->getNBDatablocks() - invertedBitCount_;
  if (endIndex > (int)correctedBits->getSize()) {
    // std::printf("invalid input\n");
    throw FormatException("invalid input data");
  }

  Table lastTable = UPPER;
  Table table = UPPER;
  int startIndex = 0;
  std::string result;
  bool end = false;
  bool shift = false;
  bool switchShift = false;
  bool binaryShift = false;

  while (!end) {
    // std::printf("decoooooding\n");

    if (shift) {
      switchShift = true;
    } else {
      lastTable = table;
    }

    int code;
    if (binaryShift) {
      if (endIndex - startIndex < 5) {
        break;
      }

      int length = readCode(correctedBits, startIndex, 5);
      startIndex += 5;
      if (length == 0) {
        if (endIndex - startIndex < 11) {
          break;
        }

        length = readCode(correctedBits, startIndex, 11) + 31;
        startIndex += 11;
      }
      for (int charCount = 0; charCount < length; charCount++) {
        if (endIndex - startIndex < 8) {
          end = true;
          break;
        }

        code = readCode(correctedBits, startIndex, 8);
        add(result, code);
        startIndex += 8;
      }
      binaryShift = false;
    } else {
      if (table == BINARY) {
        if (endIndex - startIndex < 8) {
          break;
        }
        code = readCode(correctedBits, startIndex, 8);
        startIndex += 8;

        add(result, code);
      } else {
        int size = 5;

        if (table == DIGIT) {
          size = 4;
        }

        if (endIndex - startIndex < size) {
          break;
        }

        code = readCode(correctedBits, startIndex, size);
        startIndex += size;

        const char *str = getCharacter(table, code);
        std::string string(str);
        if ((int)string.find("CTRL_") != -1) {
          table = getTable(str[5]);

          if (str[6] == 'S') {
            shift = true;
            if (str[5] == 'B') {
              binaryShift = true;
            }
          }
        } else {
          result.append(string);
        }

      }
    }

    if (switchShift) {
      table = lastTable;
      shift = false;
      switchShift = false;
    }


  }

  return Ref<String>(new String(result));

}

Ref<BitArray> Decoder::correctBits(Ref<zxing::BitArray> rawbits) {
  //return rawbits;
  // std::printf("decoding stuff:%d datablocks in %d layers\n", ddata_->getNBDatablocks(), ddata_->getNBLayers());

  Ref<GenericGF> gf = GenericGF::AZTEC_DATA_6;

  if (ddata_->getNBLayers() <= 2) {
    codewordSize_ = 6;
    gf = GenericGF::AZTEC_DATA_6;
  } else if (ddata_->getNBLayers() <= 8) {
    codewordSize_ = 8;
    gf = GenericGF::AZTEC_DATA_8;
  } else if (ddata_->getNBLayers() <= 22) {
    codewordSize_ = 10;
    gf = GenericGF::AZTEC_DATA_10;
  } else {
    codewordSize_ = 12;
    gf = GenericGF::AZTEC_DATA_12;
  }

  int numDataCodewords = ddata_->getNBDatablocks();
  int numECCodewords;
  int offset;

  if (ddata_->isCompact()) {
    offset = NB_BITS_COMPACT[ddata_->getNBLayers()] - numCodewords_ * codewordSize_;
    numECCodewords = NB_DATABLOCK_COMPACT[ddata_->getNBLayers()] - numDataCodewords;
  } else {
    offset = NB_BITS[ddata_->getNBLayers()] - numCodewords_ * codewordSize_;
    numECCodewords = NB_DATABLOCK[ddata_->getNBLayers()] - numDataCodewords;
  }

  ArrayRef<int> dataWords(numCodewords_);

  for (int i = 0; i < numCodewords_; i++) {
    int flag = 1;
    for (int j = 1; j <= codewordSize_; j++) {
      if (rawbits->get(codewordSize_ * i + codewordSize_ - j + offset)) {
        dataWords[i] += flag;
      }
      flag <<= 1;
    }

    //
    //
    //
  }

  try {
    ReedSolomonDecoder rsDecoder(gf);
    rsDecoder.decode(dataWords, numECCodewords);
  } catch (ReedSolomonException const& ignored) {
    (void)ignored;
    // std::printf("got reed solomon exception:%s, throwing formatexception\n", rse.what());
    throw FormatException("rs decoding failed");
  } catch (IllegalArgumentException const& iae) {
    (void)iae;
    // std::printf("illegal argument exception: %s", iae.what());
  }

  offset = 0;
  invertedBitCount_ = 0;

  Ref<BitArray> correctedBits(new BitArray(numDataCodewords * codewordSize_));
  for (int i = 0; i < numDataCodewords; i++) {

    bool seriesColor = false;
    int seriesCount = 0;
    int flag = 1 << (codewordSize_ - 1);

    for (int j = 0; j < codewordSize_; j++) {

      bool color = (dataWords[i] & flag) == flag;

      if (seriesCount == codewordSize_ - 1) {

        if (color == seriesColor) {
          throw FormatException("bit was not inverted");
        }

        seriesColor = false;
        seriesCount = 0;
        offset++;
        invertedBitCount_++;

      } else {

        if (seriesColor == color) {
          seriesCount++;
        } else {
          seriesCount = 1;
          seriesColor = color;
        }

        if (color) correctedBits->set(i * codewordSize_ + j - offset);

      }

      flag = ((unsigned int)flag) >> 1;

    }
  }

  return correctedBits;
}

Ref<BitArray> Decoder::extractBits(Ref<zxing::BitMatrix> matrix) {
  std::vector<bool> rawbits;

  if (ddata_->isCompact()) {
    if (ddata_->getNBLayers() > 5) { //NB_BITS_COMPACT length
      throw FormatException("data is too long");
    }
    rawbits = std::vector<bool>(NB_BITS_COMPACT[ddata_->getNBLayers()]);
    numCodewords_ = NB_DATABLOCK_COMPACT[ddata_->getNBLayers()];
  } else {
    if (ddata_->getNBLayers() > 33) { //NB_BITS length
      throw FormatException("data is too long");
    }
    rawbits = std::vector<bool>(NB_BITS[ddata_->getNBLayers()]);
    numCodewords_ = NB_DATABLOCK[ddata_->getNBLayers()];
  }

  int layer = ddata_->getNBLayers();
  int size = matrix->getHeight();
  int rawbitsOffset = 0;
  int matrixOffset = 0;


  while (layer != 0) {

    int flip = 0;
    for (int i = 0; i < 2 * size - 4; i++) {
      rawbits[rawbitsOffset + i] = matrix->get(matrixOffset + flip, matrixOffset + i / 2);
      rawbits[rawbitsOffset + 2 * size - 4 + i] = matrix->get(matrixOffset + i / 2, matrixOffset + size - 1 - flip);
      flip = (flip + 1) % 2;
    }

    flip = 0;
    for (int i = 2 * size + 1; i > 5; i--) {
      rawbits[rawbitsOffset + 4 * size - 8 + (2 * size - i) + 1] =
        matrix->get(matrixOffset + size - 1 - flip, matrixOffset + i / 2 - 1);
      rawbits[rawbitsOffset + 6 * size - 12 + (2 * size - i) + 1] =
        matrix->get(matrixOffset + i / 2 - 1, matrixOffset + flip);
      flip = (flip + 1) % 2;
    }

    matrixOffset += 2;
    rawbitsOffset += 8 * size - 16;
    layer--;
    size -= 4;

  }

  Ref<BitArray> returnValue(new BitArray((int)rawbits.size()));
  for (int i = 0; i < (int)rawbits.size(); i++) {
    if (rawbits[i]) returnValue->set(i);
  }

  return returnValue;

}

Ref<BitMatrix> Decoder::removeDashedLines(Ref<zxing::BitMatrix> matrix) {
  int nbDashed = 1 + 2 * ((matrix->getWidth() - 1) / 2 / 16);
  Ref<BitMatrix> newMatrix(new BitMatrix(matrix->getWidth() - nbDashed, matrix->getHeight() - nbDashed));

  int nx = 0;

  for (int x = 0; x < (int)matrix->getWidth(); x++) {

    if ((matrix->getWidth() / 2 - x) % 16 == 0) {
      continue;
    }

    int ny = 0;
    for (int y = 0; y < (int)matrix->getHeight(); y++) {

      if ((matrix->getWidth() / 2 - y) % 16 == 0) {
        continue;
      }

      if (matrix->get(x, y)) {
        newMatrix->set(nx, ny);
      }
      ny++;

    }
    nx++;

  }
  return newMatrix;
}

int Decoder::readCode(Ref<zxing::BitArray> rawbits, int startIndex, int length) {
  int res = 0;

  for (int i = startIndex; i < startIndex + length; i++) {
    res <<= 1;
    if (rawbits->get(i)) {
      res ++;
    }
  }

  return res;
}
}
}

// file: zxing/aztec/detector/Detector.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Detector.cpp
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

// #include <zxing/aztec/detector/Detector.h>
// #include <zxing/common/GridSampler.h>
// #include <zxing/common/detector/WhiteRectangleDetector.h>
// #include <zxing/common/reedsolomon/ReedSolomonDecoder.h>
// #include <zxing/common/reedsolomon/ReedSolomonException.h>
// #include <zxing/common/reedsolomon/GenericGF.h>
// #include <iostream>
// #include <zxing/common/detector/MathUtils.h>
// #include <zxing/NotFoundException.h>

namespace zxing {
namespace aztec {
        
Detector::Detector(Ref<BitMatrix> image):
  image_(image),
  nbLayers_(0),
  nbDataBlocks_(0),
  nbCenterLayers_(0) {

}

Ref<AztecDetectorResult> Detector::detect() {
  Ref<Point> pCenter = getMatrixCenter();

  std::vector<Ref<Point> > bullEyeCornerPoints = getBullEyeCornerPoints(pCenter);

  extractParameters(bullEyeCornerPoints);

  ArrayRef< Ref<ResultPoint> > corners = getMatrixCornerPoints(bullEyeCornerPoints);

  Ref<BitMatrix> bits =
    sampleGrid(image_,
               corners[shift_%4],
               corners[(shift_+3)%4],
               corners[(shift_+2)%4],
               corners[(shift_+1)%4]);

  // std::printf("------------\ndetected: compact:%s, nbDataBlocks:%d, nbLayers:%d\n------------\n",compact_?"YES":"NO", nbDataBlocks_, nbLayers_);

  return Ref<AztecDetectorResult>(new AztecDetectorResult(bits, corners, compact_, nbDataBlocks_, nbLayers_));
}

void Detector::extractParameters(std::vector<Ref<Point> > bullEyeCornerPoints) {
  int twoCenterLayers = 2 * nbCenterLayers_;
  // get the bits around the bull's eye
  Ref<BitArray> resab = sampleLine(bullEyeCornerPoints[0], bullEyeCornerPoints[1], twoCenterLayers+1);
  Ref<BitArray> resbc = sampleLine(bullEyeCornerPoints[1], bullEyeCornerPoints[2], twoCenterLayers+1);
  Ref<BitArray> rescd = sampleLine(bullEyeCornerPoints[2], bullEyeCornerPoints[3], twoCenterLayers+1);
  Ref<BitArray> resda = sampleLine(bullEyeCornerPoints[3], bullEyeCornerPoints[0], twoCenterLayers+1);

  // determin the orientation of the matrix
  if (resab->get(0) && resab->get(twoCenterLayers)) {
    shift_ = 0;
  } else if (resbc->get(0) && resbc->get(twoCenterLayers)) {
    shift_ = 1;
  } else if (rescd->get(0) && rescd->get(twoCenterLayers)) {
    shift_ = 2;
  } else if (resda->get(0) && resda->get(twoCenterLayers)) {
    shift_ = 3;
  } else {
    // std::printf("could not detemine orientation\n");
    throw ReaderException("could not determine orientation");
  }

  //d      a
  //
  //c      b

  //flatten the bits in a single array
  Ref<BitArray> parameterData(new BitArray(compact_?28:40));
  Ref<BitArray> shiftedParameterData(new BitArray(compact_?28:40));

  if (compact_) {
    for (int i = 0; i < 7; i++) {
      if (resab->get(2+i)) shiftedParameterData->set(i);
      if (resbc->get(2+i)) shiftedParameterData->set(i+7);
      if (rescd->get(2+i)) shiftedParameterData->set(i+14);
      if (resda->get(2+i)) shiftedParameterData->set(i+21);
    }
    for (int i = 0; i < 28; i++) {
      if (shiftedParameterData->get((i+shift_*7)%28)) parameterData->set(i);
    }

  } else {
    for (int i = 0; i < 11; i++) {
      if (i < 5) {
        if (resab->get(2+i)) shiftedParameterData->set(i);
        if (resbc->get(2+i)) shiftedParameterData->set(i+10);
        if (rescd->get(2+i)) shiftedParameterData->set(i+20);
        if (resda->get(2+i)) shiftedParameterData->set(i+30);
      }
      if (i > 5) {
        if (resab->get(2+i)) shiftedParameterData->set(i-1);
        if (resbc->get(2+i)) shiftedParameterData->set(i+9);
        if (rescd->get(2+i)) shiftedParameterData->set(i+19);
        if (resda->get(2+i)) shiftedParameterData->set(i+29);
      }
    }
    for (int i = 0; i < 40; i++) {
      if (shiftedParameterData->get((i+shift_*10)%40)) parameterData->set(i);
    }
  }

  correctParameterData(parameterData, compact_);

  getParameters(parameterData);
}

ArrayRef< Ref<ResultPoint> >
Detector::getMatrixCornerPoints(std::vector<Ref<Point> > bullEyeCornerPoints) {
  float ratio = (2 * nbLayers_ + (nbLayers_ > 4 ? 1 : 0) + (nbLayers_ - 4) / 8) / (2.0f * nbCenterLayers_);

  int dx = bullEyeCornerPoints[0]->getX() - bullEyeCornerPoints[2]->getX();
  dx += dx > 0 ? 1 : -1;
  int dy = bullEyeCornerPoints[0]->getY() - bullEyeCornerPoints[2]->getY();
  dy += dy > 0 ? 1 : -1;

  int targetcx = MathUtils::round(bullEyeCornerPoints[2]->getX() - ratio * dx);
  int targetcy = MathUtils::round(bullEyeCornerPoints[2]->getY() - ratio * dy);

  int targetax = MathUtils::round(bullEyeCornerPoints[0]->getX() + ratio * dx);
  int targetay = MathUtils::round(bullEyeCornerPoints[0]->getY() + ratio * dy);

  dx = bullEyeCornerPoints[1]->getX() - bullEyeCornerPoints[3]->getX();
  dx += dx > 0 ? 1 : -1;
  dy = bullEyeCornerPoints[1]->getY() - bullEyeCornerPoints[3]->getY();
  dy += dy > 0 ? 1 : -1;

  int targetdx = MathUtils::round(bullEyeCornerPoints[3]->getX() - ratio * dx);
  int targetdy = MathUtils::round(bullEyeCornerPoints[3]->getY() - ratio * dy);
  int targetbx = MathUtils::round(bullEyeCornerPoints[1]->getX() + ratio * dx);
  int targetby = MathUtils::round(bullEyeCornerPoints[1]->getY() + ratio * dy);

  if (!isValid(targetax, targetay) ||
      !isValid(targetbx, targetby) ||

      !isValid(targetcx, targetcy) ||
      !isValid(targetdx, targetdy)) {
    throw ReaderException("matrix extends over image bounds");
  }
  Array< Ref<ResultPoint> >* array = new Array< Ref<ResultPoint> >();
  vector< Ref<ResultPoint> >& returnValue (array->values());
  returnValue.push_back(Ref<ResultPoint>(new ResultPoint(float(targetax), float(targetay))));
  returnValue.push_back(Ref<ResultPoint>(new ResultPoint(float(targetbx), float(targetby))));
  returnValue.push_back(Ref<ResultPoint>(new ResultPoint(float(targetcx), float(targetcy))));
  returnValue.push_back(Ref<ResultPoint>(new ResultPoint(float(targetdx), float(targetdy))));
  return ArrayRef< Ref<ResultPoint> >(array);
}

void Detector::correctParameterData(Ref<zxing::BitArray> parameterData, bool compact) {
  int numCodewords;
  int numDataCodewords;

  if (compact)  {
    numCodewords = 7;
    numDataCodewords = 2;
  } else {
    numCodewords = 10;
    numDataCodewords = 4;
  }

  int numECCodewords = numCodewords - numDataCodewords;

  ArrayRef<int> parameterWords(new Array<int>(numCodewords));

  int codewordSize = 4;
  for (int i = 0; i < numCodewords; i++) {
    int flag = 1;
    for (int j = 1; j <= codewordSize; j++) {
      if (parameterData->get(codewordSize*i + codewordSize - j)) {
        parameterWords[i] += flag;
      }
      flag <<= 1;
    }
  }

  try {
    // std::printf("parameter data reed solomon\n");
    ReedSolomonDecoder rsDecoder(GenericGF::AZTEC_PARAM);
    rsDecoder.decode(parameterWords, numECCodewords);
  } catch (ReedSolomonException const& ignored) {
    (void)ignored;
    // std::printf("reed solomon decoding failed\n");
    throw ReaderException("failed to decode parameter data");
  }

  parameterData->clear();
  for (int i = 0; i < numDataCodewords; i++) {
    int flag = 1;
    for (int j = 1; j <= codewordSize; j++) {
      if ((parameterWords[i] & flag) == flag) {
        parameterData->set(i*codewordSize+codewordSize-j);
      }
      flag <<= 1;
    }
  }
}

std::vector<Ref<Point> > Detector::getBullEyeCornerPoints(Ref<zxing::aztec::Point> pCenter) {
  Ref<Point> pina = pCenter;
  Ref<Point> pinb = pCenter;
  Ref<Point> pinc = pCenter;
  Ref<Point> pind = pCenter;

  bool color = true;

  for (nbCenterLayers_ = 1; nbCenterLayers_ < 9; nbCenterLayers_++) {
    Ref<Point> pouta = getFirstDifferent(pina, color, 1, -1);
    Ref<Point> poutb = getFirstDifferent(pinb, color, 1, 1);
    Ref<Point> poutc = getFirstDifferent(pinc, color, -1, 1);
    Ref<Point> poutd = getFirstDifferent(pind, color, -1, -1);

    //d    a
    //
    //c    b

    if (nbCenterLayers_ > 2) {
      float q = distance(poutd, pouta) * nbCenterLayers_ / (distance(pind, pina) * (nbCenterLayers_ + 2));
      if (q < 0.75 || q > 1.25 || !isWhiteOrBlackRectangle(pouta, poutb, poutc, poutd)) {
        break;
      }
    }

    pina = pouta;
    pinb = poutb;
    pinc = poutc;
    pind = poutd;

    color = !color;
  }

  if (nbCenterLayers_ != 5 && nbCenterLayers_ != 7) {
    throw ReaderException("encountered wrong bullseye ring count");
  }

  compact_ = nbCenterLayers_ == 5;



  float ratio = 0.75f*2 / (2*nbCenterLayers_-3);

  int dx = pina->getX() - pind->getX();
  int dy = pina->getY() - pinc->getY();

  int targetcx = MathUtils::round(pinc->getX() - ratio * dx);
  int targetcy = MathUtils::round(pinc->getY() - ratio * dy);
  int targetax = MathUtils::round(pina->getX() + ratio * dx);
  int targetay = MathUtils::round(pina->getY() + ratio * dy);

  dx = pinb->getX() - pind->getX();
  dy = pinb->getY() - pind->getY();

  int targetdx = MathUtils::round(pind->getX() - ratio * dx);
  int targetdy = MathUtils::round(pind->getY() - ratio * dy);
  int targetbx = MathUtils::round(pinb->getX() + ratio * dx);
  int targetby = MathUtils::round(pinb->getY() + ratio * dy);

  if (!isValid(targetax, targetay) ||
      !isValid(targetbx, targetby) ||
      !isValid(targetcx, targetcy) ||
      !isValid(targetdx, targetdy)) {
    throw ReaderException("bullseye extends over image bounds");
  }

  std::vector<Ref<Point> > returnValue;
  returnValue.push_back(Ref<Point>(new Point(targetax, targetay)));
  returnValue.push_back(Ref<Point>(new Point(targetbx, targetby)));
  returnValue.push_back(Ref<Point>(new Point(targetcx, targetcy)));
  returnValue.push_back(Ref<Point>(new Point(targetdx, targetdy)));

  return returnValue;

}

Ref<Point> Detector::getMatrixCenter() {
  Ref<ResultPoint> pointA, pointB, pointC, pointD;
  try {

    std::vector<Ref<ResultPoint> > cornerPoints = WhiteRectangleDetector(image_).detect();
    pointA = cornerPoints[0];
    pointB = cornerPoints[1];
    pointC = cornerPoints[2];
    pointD = cornerPoints[3];

  } catch (NotFoundException const& e) {
    (void)e;

    int cx = image_->getWidth() / 2;
    int cy = image_->getHeight() / 2;

    pointA = getFirstDifferent(Ref<Point>(new Point(cx+7, cy-7)), false,  1, -1)->toResultPoint();
    pointB = getFirstDifferent(Ref<Point>(new Point(cx+7, cy+7)), false,  1,  1)->toResultPoint();
    pointC = getFirstDifferent(Ref<Point>(new Point(cx-7, cy+7)), false, -1, -1)->toResultPoint();
    pointD = getFirstDifferent(Ref<Point>(new Point(cx-7, cy-7)), false, -1, -1)->toResultPoint();

  }

  int cx = MathUtils::round((pointA->getX() + pointD->getX() + pointB->getX() + pointC->getX()) / 4.0f);
  int cy = MathUtils::round((pointA->getY() + pointD->getY() + pointB->getY() + pointC->getY()) / 4.0f);

  try {

    std::vector<Ref<ResultPoint> > cornerPoints = WhiteRectangleDetector(image_, 15, cx, cy).detect();
    pointA = cornerPoints[0];
    pointB = cornerPoints[1];
    pointC = cornerPoints[2];
    pointD = cornerPoints[3];

  } catch (NotFoundException const& e) {
    (void)e;

    pointA = getFirstDifferent(Ref<Point>(new Point(cx+7, cy-7)), false,  1, -1)->toResultPoint();
    pointB = getFirstDifferent(Ref<Point>(new Point(cx+7, cy+7)), false,  1,  1)->toResultPoint();
    pointC = getFirstDifferent(Ref<Point>(new Point(cx-7, cy+7)), false, -1, 1)->toResultPoint();
    pointD = getFirstDifferent(Ref<Point>(new Point(cx-7, cy-7)), false, -1, -1)->toResultPoint();

  }

  cx = MathUtils::round((pointA->getX() + pointD->getX() + pointB->getX() + pointC->getX()) / 4.0f);
  cy = MathUtils::round((pointA->getY() + pointD->getY() + pointB->getY() + pointC->getY()) / 4.0f);

  return Ref<Point>(new Point(cx, cy));

}

Ref<BitMatrix> Detector::sampleGrid(Ref<zxing::BitMatrix> image,
                                    Ref<zxing::ResultPoint> topLeft,
                                    Ref<zxing::ResultPoint> bottomLeft,
                                    Ref<zxing::ResultPoint> bottomRight,
                                    Ref<zxing::ResultPoint> topRight) {
  int dimension;
  if (compact_) {
    dimension = 4 * nbLayers_+11;
  } else {
    if (nbLayers_ <= 4) {
      dimension = 4 * nbLayers_ + 15;
    } else {
      dimension = 4 * nbLayers_ + 2 * ((nbLayers_-4)/8 + 1) + 15;
    }
  }

  GridSampler sampler = GridSampler::getInstance();

  return sampler.sampleGrid(image,
                            dimension,
                            0.5f,
                            0.5f,
                            dimension - 0.5f,
                            0.5f,
                            dimension - 0.5f,
                            dimension - 0.5f,
                            0.5f,
                            dimension - 0.5f,
                            topLeft->getX(),
                            topLeft->getY(),
                            topRight->getX(),
                            topRight->getY(),
                            bottomRight->getX(),
                            bottomRight->getY(),
                            bottomLeft->getX(),
                            bottomLeft->getY());
}

void Detector::getParameters(Ref<zxing::BitArray> parameterData) {
  nbLayers_ = 0;
  nbDataBlocks_ = 0;

  int nbBitsForNbLayers;
  int nbBitsForNbDatablocks;

  if (compact_) {
    nbBitsForNbLayers = 2;
    nbBitsForNbDatablocks = 6;
  } else {
    nbBitsForNbLayers = 5;
    nbBitsForNbDatablocks = 11;
  }

  for (int i = 0; i < nbBitsForNbLayers; i++) {
    nbLayers_ <<= 1;
    if (parameterData->get(i)) {
      nbLayers_++;
    }
  }

  for (int i = nbBitsForNbLayers; i < nbBitsForNbLayers + nbBitsForNbDatablocks; i++) {
    nbDataBlocks_ <<= 1;
    if (parameterData->get(i)) {
      nbDataBlocks_++;
    }
  }

  nbLayers_++;
  nbDataBlocks_++;
}

Ref<BitArray> Detector::sampleLine(Ref<zxing::aztec::Point> p1, Ref<zxing::aztec::Point> p2, int size) {
  Ref<BitArray> res(new BitArray(size));

  float d = distance(p1, p2);
  float moduleSize = d / (size-1);
  float dx = moduleSize * float(p2->getX() - p1->getX())/d;
  float dy = moduleSize * float(p2->getY() - p1->getY())/d;

  float px = float(p1->getX());
  float py = float(p1->getY());

  for (int i = 0; i < size; i++) {
    if (image_->get(MathUtils::round(px), MathUtils::round(py))) res->set(i);
    px+=dx;
    py+=dy;
  }

  return res;
}

bool Detector::isWhiteOrBlackRectangle(Ref<zxing::aztec::Point> p1,
                                       Ref<zxing::aztec::Point> p2,
                                       Ref<zxing::aztec::Point> p3,
                                       Ref<zxing::aztec::Point> p4) {
  int corr = 3;

  p1 = new Point(p1->getX() - corr, p1->getY() + corr);
  p2 = new Point(p2->getX() - corr, p2->getY() - corr);
  p3 = new Point(p3->getX() + corr, p3->getY() - corr);
  p4 = new Point(p4->getX() + corr, p4->getY() + corr);

  int cInit = getColor(p4, p1);

  if (cInit == 0) {
    return false;
  }

  int c = getColor(p1, p2);

  if (c != cInit) {
    return false;
  }

  c = getColor(p2, p3);

  if (c != cInit) {
    return false;
  }

  c = getColor(p3, p4);

  if (c != cInit) {
    return false;
  }

  return true;
}

int Detector::getColor(Ref<zxing::aztec::Point> p1, Ref<zxing::aztec::Point> p2) {
  float d = distance(p1, p2);

  float dx = (p2->getX() - p1->getX()) / d;
  float dy = (p2->getY() - p1->getY()) / d;

  int error = 0;

  float px = float(p1->getX());
  float py = float(p1->getY());

  bool colorModel = image_->get(p1->getX(), p1->getY());

  for (int i = 0; i < d; i++) {
    px += dx;
    py += dy;
    if (image_->get(MathUtils::round(px), MathUtils::round(py)) != colorModel) {
      error ++;
    }
  }

  float errRatio = (float)error/d;


  if (errRatio > 0.1f && errRatio < 0.9f) {
    return 0;
  }

  return (errRatio <= 0.1) == colorModel ? 1 : -1;
}

Ref<Point> Detector::getFirstDifferent(Ref<zxing::aztec::Point> init, bool color, int dx, int dy) {
  int x = init->getX() + dx;
  int y = init->getY() + dy;

  while (isValid(x, y) && image_->get(x, y) == color) {
    x += dx;
    y += dy;
  }

  x -= dx;
  y -= dy;

  while (isValid(x, y) && image_->get(x, y) == color) {
    x += dx;
  }

  x -= dx;

  while (isValid(x, y) && image_->get(x, y) == color) {
    y += dy;
  }

  y -= dy;

  return Ref<Point>(new Point(x, y));
}

bool Detector::isValid(int x, int y) {
  return x >= 0 && x < (int)image_->getWidth() && y > 0 && y < (int)image_->getHeight();
}

float Detector::distance(Ref<zxing::aztec::Point> a, Ref<zxing::aztec::Point> b) {
  return sqrtf((float)((a->getX() - b->getX()) * (a->getX() - b->getX()) + (a->getY() - b->getY()) * (a->getY() - b->getY())));
}
}
}

// file: zxing/common/BitArray.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/common/BitArray.h>

namespace zxing {
    
int BitArray::makeArraySize(int size) {
  return (size + bitsPerWord-1) >> logBits;
}

BitArray::BitArray(int size_)
  : size(size_), bits(makeArraySize(size)) {}

BitArray::~BitArray() {
}

int BitArray::getSize() const {
  return size;
}

void BitArray::setBulk(int i, int newBits) {
  bits[i >> logBits] = newBits;
}

void BitArray::clear() {
  size_t max = bits->size();
  for (size_t i = 0; i < max; i++) {
    bits[(int)i] = 0;
  }
}

bool BitArray::isRange(int start, int end, bool value) {
  if (end < start) {
    throw IllegalArgumentException();
  }
  if (end == start) {
    return true; // empty range matches
  }
  end--; // will be easier to treat this as the last actually set bit -- inclusive
  int firstInt = start >> logBits;
  int lastInt = end >> logBits;
  for (int i = firstInt; i <= lastInt; i++) {
    int firstBit = i > firstInt ? 0 : start & bitsMask;
    int lastBit = i < lastInt ? (bitsPerWord-1) : end & bitsMask;
    int mask;
    if (firstBit == 0 && lastBit == (bitsPerWord-1)) {
      mask = -1;
    } else {
      mask = 0;
      for (int j = firstBit; j <= lastBit; j++) {
        mask |= 1 << j;
      }
    }

    // Return false if we're looking for 1s and the masked bits[i] isn't all 1s (that is,
    // equals the mask, or we're looking for 0s and the masked portion is not all 0s
    if ((bits[i] & mask) != (value ? mask : 0)) {
      return false;
    }
  }
  return true;
}

vector<int>& BitArray::getBitArray() {
  return bits->values();
}

void BitArray::reverse() {
  ArrayRef<int> newBits((int)bits->size());
  int size = this->size;
  for (int i = 0; i < size; i++) {
    if (get(size - i - 1)) {
      newBits[i >> logBits] |= 1 << (i & bitsMask);
    }
  }
  bits = newBits;
}

BitArray::Reverse::Reverse(Ref<BitArray> array_) : array(array_) {
  array->reverse();
}

BitArray::Reverse::~Reverse() {
  array->reverse();
}

namespace {
  // N.B.: This only works for 32 bit ints ...
  int numberOfTrailingZeros(int i) {
    // HD, Figure 5-14
    int y;
    if (i == 0) return 32;
    int n = 31;
    y = i <<16; if (y != 0) { n = n -16; i = y; }
    y = i << 8; if (y != 0) { n = n - 8; i = y; }
    y = i << 4; if (y != 0) { n = n - 4; i = y; }
    y = i << 2; if (y != 0) { n = n - 2; i = y; }
    return n - (((unsigned int)(i << 1)) >> 31);
  }
}

int BitArray::getNextSet(int from) {
  if (from >= size) {
    return size;
  }
  int bitsOffset = from >> logBits;
  int currentBits = bits[bitsOffset];
  // mask off lesser bits first
  currentBits &= ~((1 << (from & bitsMask)) - 1);
  while (currentBits == 0) {
    if (++bitsOffset == (int)bits->size()) {
      return size;
    }
    currentBits = bits[bitsOffset];
  }
  int result = (bitsOffset << logBits) + numberOfTrailingZeros(currentBits);
  return result > size ? size : result;
}

int BitArray::getNextUnset(int from) {
  if (from >= size) {
    return size;
  }
  int bitsOffset = from >> logBits;
  int currentBits = ~bits[bitsOffset];
  // mask off lesser bits first
  currentBits &= ~((1 << (from & bitsMask)) - 1);
  while (currentBits == 0) {
    if (++bitsOffset == (int)bits->size()) {
      return size;
    }
    currentBits = ~bits[bitsOffset];
  }
  int result = (bitsOffset << logBits) + numberOfTrailingZeros(currentBits);
  return result > size ? size : result;
}
}

// file: zxing/common/BitArrayIO.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/common/BitArray.h>

namespace zxing {
    
ostream& operator << (ostream& os, BitArray const& ba) {
  for (int i = 0, size = ba.getSize(); i < size; i++) {
    if ((i & 0x07) == 0) {
      os << ' ';
    }
    os << (ba.get(i) ? 'X' : '.');
  }
  return os;
}
}

// file: zxing/common/BitMatrix.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/common/BitMatrix.h>
// #include <zxing/common/IllegalArgumentException.h>

// #include <iostream>
// #include <sstream>
// #include <string>

namespace zxing {
    
void BitMatrix::init(int width, int height) {
  if (width < 1 || height < 1) {
    throw IllegalArgumentException("Both dimensions must be greater than 0");
  }
  this->width = width;
  this->height = height;
  this->rowSize = (width + bitsPerWord - 1) >> logBits;
  bits = ArrayRef<int>(rowSize * height);
}

BitMatrix::BitMatrix(int dimension) {
  init(dimension, dimension);
}

BitMatrix::BitMatrix(int width, int height) {
  init(width, height);
}

BitMatrix::~BitMatrix() {}

void BitMatrix::flip(size_t x, size_t y) {
  int offset = (int)(y * rowSize + (x >> logBits));
  bits[offset] ^= 1 << (x & bitsMask);
}

void BitMatrix::setRegion(int left, int top, int width, int height) {
  if (top < 0 || left < 0) {
    throw IllegalArgumentException("Left and top must be nonnegative");
  }
  if (height < 1 || width < 1) {
    throw IllegalArgumentException("Height and width must be at least 1");
  }
  int right = left + width;
  int bottom = top + height;
  if (bottom > this->height || right > this->width) {
    throw IllegalArgumentException("The region must fit inside the matrix");
  }
  for (int y = top; y < bottom; y++) {
    int offset = y * rowSize;
    for (int x = left; x < right; x++) {
      bits[offset + (x >> logBits)] |= 1 << (x & bitsMask);
    }
  }
}

Ref<BitArray> BitMatrix::getRow(int y, Ref<BitArray> row) {
  if (row.empty() || row->getSize() < width) {
    row = new BitArray(width);
  }
  int offset = y * rowSize;
  for (int x = 0; x < rowSize; x++) {
    row->setBulk(x << logBits, bits[offset + x]);
  }
  return row;
}

int BitMatrix::getWidth() const {
  return width;
}

int BitMatrix::getHeight() const {
  return height;
}

ArrayRef<int> BitMatrix::getTopLeftOnBit() const {
  int bitsOffset = 0;
  while (bitsOffset < bits->size() && bits[bitsOffset] == 0) {
    bitsOffset++;
  }
  if (bitsOffset == bits->size()) {
    return ArrayRef<int>();
  }
  int y = bitsOffset / rowSize;
  int x = (bitsOffset % rowSize) << 5;

  int theBits = bits[bitsOffset];
  int bit = 0;
  while ((theBits << (31-bit)) == 0) {
    bit++;
  }
  x += bit;
  ArrayRef<int> res (2);
  res[0]=x;
  res[1]=y;
  return res;
}

ArrayRef<int> BitMatrix::getBottomRightOnBit() const {
  int bitsOffset = (int)bits->size() - 1;
  while (bitsOffset >= 0 && bits[bitsOffset] == 0) {
    bitsOffset--;
  }
  if (bitsOffset < 0) {
    return ArrayRef<int>();
  }

  int y = bitsOffset / rowSize;
  int x = (bitsOffset % rowSize) << 5;

  int theBits = bits[bitsOffset];
  int bit = 31;
  while ((theBits >> bit) == 0) {
    bit--;
  }
  x += bit;

  ArrayRef<int> res (2);
  res[0]=x;
  res[1]=y;
  return res;
}
}

// file: zxing/common/BitSource.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  BitSource.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 09/05/2008.
 *  Copyright 2008 Google UK. All rights reserved.
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

// #include <zxing/common/BitSource.h>
// #include <sstream>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {

int BitSource::readBits(int numBits) {
  if (numBits < 0 || numBits > 32 || numBits > available()) {
    std::ostringstream oss;
    oss << numBits;
    throw IllegalArgumentException(oss.str().c_str());
  }

  int result = 0;

  // First, read remainder from current byte
  if (bitOffset_ > 0) {
    int bitsLeft = 8 - bitOffset_;
    int toRead = numBits < bitsLeft ? numBits : bitsLeft;
    int bitsToNotRead = bitsLeft - toRead;
    int mask = (0xFF >> (8 - toRead)) << bitsToNotRead;
    result = (bytes_[byteOffset_] & mask) >> bitsToNotRead;
    numBits -= toRead;
    bitOffset_ += toRead;
    if (bitOffset_ == 8) {
      bitOffset_ = 0;
      byteOffset_++;
    }
  }

  // Next read whole bytes
  if (numBits > 0) {
    while (numBits >= 8) {
      result = (result << 8) | (bytes_[byteOffset_] & 0xFF);
      byteOffset_++;
      numBits -= 8;
    }


    // Finally read a partial byte
    if (numBits > 0) {
      int bitsToNotRead = 8 - numBits;
      int mask = (0xFF >> bitsToNotRead) << bitsToNotRead;
      result = (result << numBits) | ((bytes_[byteOffset_] & mask) >> bitsToNotRead);
      bitOffset_ += numBits;
    }
  }

  return result;
}

int BitSource::available() {
  return (int)(8 * (bytes_->size() - byteOffset_) - bitOffset_);
}
}

// file: zxing/common/CharacterSetECI.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/common/CharacterSetECI.h>
// #include <zxing/common/IllegalArgumentException.h>
// #include <zxing/FormatException.h>

namespace zxing {
namespace common {
        
std::map<int, zxing::Ref<CharacterSetECI> > CharacterSetECI::VALUE_TO_ECI;
std::map<std::string, zxing::Ref<CharacterSetECI> > CharacterSetECI::NAME_TO_ECI;

const bool CharacterSetECI::inited = CharacterSetECI::init_tables();

#define ADD_CHARACTER_SET(VALUES, STRINGS) \
  { static int values[] = {VALUES, -1}; \
    static char const* strings[] = {STRINGS, 0}; \
    addCharacterSet(values, strings); }

#define XC ,

bool CharacterSetECI::init_tables() {
  ADD_CHARACTER_SET(0 XC 2, "Cp437");
  ADD_CHARACTER_SET(1 XC 3, "ISO8859_1" XC "ISO-8859-1");
  ADD_CHARACTER_SET(4, "ISO8859_2" XC "ISO-8859-2");
  ADD_CHARACTER_SET(5, "ISO8859_3" XC "ISO-8859-3");
  ADD_CHARACTER_SET(6, "ISO8859_4" XC "ISO-8859-4");
  ADD_CHARACTER_SET(7, "ISO8859_5" XC "ISO-8859-5");
  ADD_CHARACTER_SET(8, "ISO8859_6" XC "ISO-8859-6");
  ADD_CHARACTER_SET(9, "ISO8859_7" XC "ISO-8859-7");
  ADD_CHARACTER_SET(10, "ISO8859_8" XC "ISO-8859-8");
  ADD_CHARACTER_SET(11, "ISO8859_9" XC "ISO-8859-9");
  ADD_CHARACTER_SET(12, "ISO8859_10" XC "ISO-8859-10");
  ADD_CHARACTER_SET(13, "ISO8859_11" XC "ISO-8859-11");
  ADD_CHARACTER_SET(15, "ISO8859_13" XC "ISO-8859-13");
  ADD_CHARACTER_SET(16, "ISO8859_14" XC "ISO-8859-14");
  ADD_CHARACTER_SET(17, "ISO8859_15" XC "ISO-8859-15");
  ADD_CHARACTER_SET(18, "ISO8859_16" XC "ISO-8859-16");
  ADD_CHARACTER_SET(20, "SJIS" XC "Shift_JIS");
  ADD_CHARACTER_SET(21, "Cp1250" XC "windows-1250");
  ADD_CHARACTER_SET(22, "Cp1251" XC "windows-1251");
  ADD_CHARACTER_SET(23, "Cp1252" XC "windows-1252");
  ADD_CHARACTER_SET(24, "Cp1256" XC "windows-1256");
  ADD_CHARACTER_SET(25, "UnicodeBigUnmarked" XC "UTF-16BE" XC "UnicodeBig");
  ADD_CHARACTER_SET(26, "UTF8" XC "UTF-8");
  ADD_CHARACTER_SET(27 XC 170, "ASCII" XC "US-ASCII");
  ADD_CHARACTER_SET(28, "Big5");
  ADD_CHARACTER_SET(29, "GB18030" XC "GB2312" XC "EUC_CN" XC "GBK");
  ADD_CHARACTER_SET(30, "EUC_KR" XC "EUC-KR");
  return true;
}

#undef XC

CharacterSetECI::CharacterSetECI(int const* values,
                                 char const* const* names)
  : values_(values), names_(names) {
  zxing::Ref<CharacterSetECI> this_ref(this);
  for(int const* values = values_; *values != -1; values++) {
    VALUE_TO_ECI[*values] = this_ref;
  }
  for(char const* const* names = names_; *names; names++) {
    NAME_TO_ECI[string(*names)] = this_ref;
  }
}

char const* CharacterSetECI::name() const {
  return names_[0];
}

int CharacterSetECI::getValue() const {
  return values_[0];
}

void CharacterSetECI::addCharacterSet(int const* values, char const* const* names) {
  new CharacterSetECI(values, names);
}

CharacterSetECI* CharacterSetECI::getCharacterSetECIByValue(int value) {
  if (value < 0 || value >= 900) {
    throw FormatException();
  }
  return VALUE_TO_ECI[value];
}

CharacterSetECI* CharacterSetECI::getCharacterSetECIByName(string const& name) {
  return NAME_TO_ECI[name];
}
}
}

// file: zxing/common/DecoderResult.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  DecoderResult.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 20/05/2008.
 *  Copyright 2008-2011 ZXing authors All rights reserved.
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

// #include <zxing/common/DecoderResult.h>

namespace zxing {
    
DecoderResult::DecoderResult(ArrayRef<char> rawBytes,
                             Ref<String> text,
                             ArrayRef< ArrayRef<char> >& byteSegments,
                             string const& ecLevel) :
  rawBytes_(rawBytes),
  text_(text),
  byteSegments_(byteSegments),
  ecLevel_(ecLevel) {}

DecoderResult::DecoderResult(ArrayRef<char> rawBytes,
                             Ref<String> text)
  : rawBytes_(rawBytes), text_(text) {}

ArrayRef<char> DecoderResult::getRawBytes() {
  return rawBytes_;
}

Ref<String> DecoderResult::getText() {
  return text_;
}
}

// file: zxing/common/DetectorResult.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  DetectorResult.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 14/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

namespace zxing {

DetectorResult::DetectorResult(Ref<BitMatrix> bits,
                               ArrayRef< Ref<ResultPoint> > points)
  : bits_(bits), points_(points) {
}

Ref<BitMatrix> DetectorResult::getBits() {
  return bits_;
}

ArrayRef< Ref<ResultPoint> > DetectorResult::getPoints() {
  return points_;
}

}

// file: zxing/common/GlobalHistogramBinarizer.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  GlobalHistogramBinarizer.cpp
 *  zxing
 *
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

// #include <zxing/common/GlobalHistogramBinarizer.h>
// #include <zxing/NotFoundException.h>
// #include <zxing/common/Array.h>

namespace zxing {
    
namespace {
  const int LUMINANCE_BITS = 5;
  const int LUMINANCE_SHIFT = 8 - LUMINANCE_BITS;
  const int LUMINANCE_BUCKETS = 1 << LUMINANCE_BITS;
  const ArrayRef<char> EMPTY (0);
}

GlobalHistogramBinarizer::GlobalHistogramBinarizer(Ref<LuminanceSource> source)
  : Binarizer(source), luminances(EMPTY), buckets(LUMINANCE_BUCKETS) {}

GlobalHistogramBinarizer::~GlobalHistogramBinarizer() {}

void GlobalHistogramBinarizer::initArrays(int luminanceSize) {
  if (luminances->size() < luminanceSize) {
    luminances = ArrayRef<char>(luminanceSize);
  }
  for (int x = 0; x < LUMINANCE_BUCKETS; x++) {
    buckets[x] = 0;
  }
}

Ref<BitArray> GlobalHistogramBinarizer::getBlackRow(int y, Ref<BitArray> row) {
  // std::cerr << "gbr " << y << std::endl;
  LuminanceSource& source = *getLuminanceSource();
  int width = source.getWidth();
  if (row == NULL || static_cast<int>(row->getSize()) < width) {
    row = new BitArray(width);
  } else {
    row->clear();
  }

  initArrays(width);
  ArrayRef<char> localLuminances = source.getRow(y, luminances);
  if (false) {
    std::cerr << "gbr " << y << " r ";
    for(int i=0, e=localLuminances->size(); i < e; ++i) {
      std::cerr << 0+localLuminances[i] << " ";
    }
    std::cerr << std::endl;
  }
  ArrayRef<int> localBuckets = buckets;
  for (int x = 0; x < width; x++) {
    int pixel = localLuminances[x] & 0xff;
    localBuckets[pixel >> LUMINANCE_SHIFT]++;
  }
  int blackPoint = estimateBlackPoint(localBuckets);
  // std::cerr << "gbr bp " << y << " " << blackPoint << std::endl;

  int left = localLuminances[0] & 0xff;
  int center = localLuminances[1] & 0xff;
  for (int x = 1; x < width - 1; x++) {
    int right = localLuminances[x + 1] & 0xff;
    // A simple -1 4 -1 box filter with a weight of 2.
    int luminance = ((center << 2) - left - right) >> 1;
    if (luminance < blackPoint) {
      row->set(x);
    }
    left = center;
    center = right;
  }
  return row;
}

Ref<BitMatrix> GlobalHistogramBinarizer::getBlackMatrix() {
  LuminanceSource& source = *getLuminanceSource();
  int width = source.getWidth();
  int height = source.getHeight();
  Ref<BitMatrix> matrix(new BitMatrix(width, height));

  // Quickly calculates the histogram by sampling four rows from the image.
  // This proved to be more robust on the blackbox tests than sampling a
  // diagonal as we used to do.
  initArrays(width);
  ArrayRef<int> localBuckets = buckets;
  for (int y = 1; y < 5; y++) {
    int row = height * y / 5;
    ArrayRef<char> localLuminances = source.getRow(row, luminances);
    int right = (width << 2) / 5;
    for (int x = width / 5; x < right; x++) {
      int pixel = localLuminances[x] & 0xff;
      localBuckets[pixel >> LUMINANCE_SHIFT]++;
    }
  }

  int blackPoint = estimateBlackPoint(localBuckets);

  ArrayRef<char> localLuminances = source.getMatrix();
  for (int y = 0; y < height; y++) {
    int offset = y * width;
    for (int x = 0; x < width; x++) {
      int pixel = localLuminances[offset + x] & 0xff;
      if (pixel < blackPoint) {
        matrix->set(x, y);
      }
    }
  }

  return matrix;
}

using namespace std;

int GlobalHistogramBinarizer::estimateBlackPoint(ArrayRef<int> const& buckets) {
  // Find tallest peak in histogram
  size_t numBuckets = buckets->size();
  int maxBucketCount = 0;
  int firstPeak = 0;
  int firstPeakSize = 0;
  if (false) {
    for (int x = 0; x < numBuckets; x++) {
      cerr << buckets[x] << " ";
    }
    cerr << endl;
  }
  for (int x = 0; x < numBuckets; x++) {
    if (buckets[x] > firstPeakSize) {
      firstPeak = x;
      firstPeakSize = buckets[x];
    }
    if (buckets[x] > maxBucketCount) {
      maxBucketCount = buckets[x];
    }
  }

  // Find second-tallest peak -- well, another peak that is tall and not
  // so close to the first one
  int secondPeak = 0;
  int secondPeakScore = 0;
  for (int x = 0; x < numBuckets; x++) {
    int distanceToBiggest = x - firstPeak;
    // Encourage more distant second peaks by multiplying by square of distance
    int score = buckets[x] * distanceToBiggest * distanceToBiggest;
    if (score > secondPeakScore) {
      secondPeak = x;
      secondPeakScore = score;
    }
  }

  if (firstPeak > secondPeak) {
    int temp = firstPeak;
    firstPeak = secondPeak;
    secondPeak = temp;
  }

  // Kind of arbitrary; if the two peaks are very close, then we figure there is
  // so little dynamic range in the image, that discriminating black and white
  // is too error-prone.
  // Decoding the image/line is either pointless, or may in some cases lead to
  // a false positive for 1D formats, which are relatively lenient.
  // We arbitrarily say "close" is
  // "<= 1/16 of the total histogram buckets apart"
  // std::cerr << "! " << secondPeak << " " << firstPeak << " " << numBuckets << std::endl;
  if (secondPeak - firstPeak <= numBuckets >> 4) {
    throw NotFoundException();
  }

  // Find a valley between them that is low and closer to the white peak
  int bestValley = secondPeak - 1;
  int bestValleyScore = -1;
  for (int x = secondPeak - 1; x > firstPeak; x--) {
    int fromFirst = x - firstPeak;
    // Favor a "valley" that is not too close to either peak -- especially not
    // the black peak -- and that has a low value of course
    int score = fromFirst * fromFirst * (secondPeak - x) *
      (maxBucketCount - buckets[x]);
    if (score > bestValleyScore) {
      bestValley = x;
      bestValleyScore = score;
    }
  }

  // std::cerr << "bps " << (bestValley << LUMINANCE_SHIFT) << std::endl;
  return bestValley << LUMINANCE_SHIFT;
}

Ref<Binarizer> GlobalHistogramBinarizer::createBinarizer(Ref<LuminanceSource> source) {
  return Ref<Binarizer> (new GlobalHistogramBinarizer(source));
}
}

// file: zxing/common/GreyscaleLuminanceSource.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  GreyscaleLuminanceSource.cpp
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

// #include <zxing/common/GreyscaleLuminanceSource.h>
// #include <zxing/common/GreyscaleRotatedLuminanceSource.h>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {

GreyscaleLuminanceSource::
GreyscaleLuminanceSource(ArrayRef<char> greyData,
                         int dataWidth, int dataHeight,
                         int left, int top,
                         int width, int height,
                         bool inverse)
    : Super(width, height),
      greyData_(greyData),
      dataWidth_(dataWidth), dataHeight_(dataHeight),
      left_(left), top_(top), inverse_(inverse) {

  if (left + width > dataWidth || top + height > dataHeight || top < 0 || left < 0) {
    throw IllegalArgumentException("Crop rectangle does not fit within image data.");
  }
}

ArrayRef<char> GreyscaleLuminanceSource::getRow(int y, ArrayRef<char> row) const {
  if (y < 0 || y >= this->getHeight()) {
    throw IllegalArgumentException("Requested row is outside the image.");
  }
  int width = getWidth();
  if (!row || row->size() < width) {
    ArrayRef<char> temp (width);
    row = temp;
  }
  int offset = (y + top_) * dataWidth_ + left_;
  memcpy(&row[0], &greyData_[offset], width);
  return row;
}

ArrayRef<char> GreyscaleLuminanceSource::getMatrix() const {
  int size = getWidth() * getHeight();
  ArrayRef<char> result (size);
  if (left_ == 0 && top_ == 0 && dataWidth_ == getWidth() && dataHeight_ == getHeight()) {
    memcpy(&result[0], &greyData_[0], size);
  } else {
    for (int row = 0; row < getHeight(); row++) {
      memcpy(&result[row * getWidth()], &greyData_[(top_ + row) * dataWidth_ + left_], getWidth());
    }
  }

  if (inverse_) {
    for (int i = 0; i < size; i++) {
      result[i] = static_cast<unsigned char>(255 - result[i]);;
    }
  }

  return result;
}

Ref<LuminanceSource> GreyscaleLuminanceSource::rotateCounterClockwise() const {
  // Intentionally flip the left, top, width, and height arguments as
  // needed. dataWidth and dataHeight are always kept unrotated.
  Ref<LuminanceSource> result (
      new GreyscaleRotatedLuminanceSource(greyData_,
                                          dataWidth_, dataHeight_,
                                          top_, left_, getHeight(), getWidth()));
  return result;
}
}

// file: zxing/common/GreyscaleRotatedLuminanceSource.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  GreyscaleRotatedLuminanceSource.cpp
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


// #include <zxing/common/GreyscaleRotatedLuminanceSource.h>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
    
// Note that dataWidth and dataHeight are not reversed, as we need to
// be able to traverse the greyData correctly, which does not get
// rotated.
GreyscaleRotatedLuminanceSource::
GreyscaleRotatedLuminanceSource(ArrayRef<char> greyData,
                                int dataWidth, int dataHeight,
                                int left, int top,
                                int width, int height)
    : Super(width, height),
      greyData_(greyData),
      dataWidth_(dataWidth),
      left_(left), top_(top) {
  // Intentionally comparing to the opposite dimension since we're rotated.
  if (left + width > dataHeight || top + height > dataWidth) {
    throw IllegalArgumentException("Crop rectangle does not fit within image data.");
  }
}

// The API asks for rows, but we're rotated, so we return columns.
ArrayRef<char>
GreyscaleRotatedLuminanceSource::getRow(int y, ArrayRef<char> row) const {
  if (y < 0 || y >= getHeight()) {
    throw IllegalArgumentException("Requested row is outside the image.");
  }
  if (!row || row->size() < getWidth()) {
    row = ArrayRef<char>(getWidth());
  }
  int offset = (left_ * dataWidth_) + (dataWidth_ - 1 - (y + top_));
  using namespace std;
  if (false) {
    cerr << offset << " = "
         << top_ << " " << left_ << " "
         << getHeight() << " " << getWidth() << " "
         << y << endl;
  }
  for (int x = 0; x < getWidth(); x++) {
    row[x] = greyData_[offset];
    offset += dataWidth_;
  }
  return row;
}

ArrayRef<char> GreyscaleRotatedLuminanceSource::getMatrix() const {
  ArrayRef<char> result (getWidth() * getHeight());
  for (int y = 0; y < getHeight(); y++) {
    char* row = &result[y * getWidth()];
    int offset = (left_ * dataWidth_) + (dataWidth_ - 1 - (y + top_));
    for (int x = 0; x < getWidth(); x++) {
      row[x] = greyData_[offset];
      offset += dataWidth_;
    }
  }
  return result;
}
}

// file: zxing/common/GridSampler.cpp

/*
 *  GridSampler.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 18/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/common/GridSampler.h>
// #include <zxing/common/PerspectiveTransform.h>
// #include <zxing/ReaderException.h>
// #include <iostream>
// #include <sstream>

namespace zxing {
using namespace std;

GridSampler GridSampler::gridSampler;

GridSampler::GridSampler() {
}

Ref<BitMatrix> GridSampler::sampleGrid(Ref<BitMatrix> image, int dimension, Ref<PerspectiveTransform> transform) {
  Ref<BitMatrix> bits(new BitMatrix(dimension));
  vector<float> points(dimension << 1, (const float)0.0f);
  for (int y = 0; y < dimension; y++) {
    int max = (int)points.size();
    float yValue = (float)y + 0.5f;
    for (int x = 0; x < max; x += 2) {
      points[x] = (float)(x >> 1) + 0.5f;
      points[x + 1] = yValue;
    }
    transform->transformPoints(points);
    checkAndNudgePoints(image, points);
    for (int x = 0; x < max; x += 2) {
      if (image->get((int)points[x], (int)points[x + 1])) {
        bits->set(x >> 1, y);
      }
    }
  }
  return bits;
}

Ref<BitMatrix> GridSampler::sampleGrid(Ref<BitMatrix> image, int dimensionX, int dimensionY, Ref<PerspectiveTransform> transform) {
  Ref<BitMatrix> bits(new BitMatrix(dimensionX, dimensionY));
  vector<float> points(dimensionX << 1, (const float)0.0f);
  for (int y = 0; y < dimensionY; y++) {
    int max = (int)points.size();
    float yValue = (float)y + 0.5f;
    for (int x = 0; x < max; x += 2) {
      points[x] = (float)(x >> 1) + 0.5f;
      points[x + 1] = yValue;
    }
    transform->transformPoints(points);
    checkAndNudgePoints(image, points);
    for (int x = 0; x < max; x += 2) {
      if (image->get((int)points[x], (int)points[x + 1])) {
        bits->set(x >> 1, y);
      }
    }
  }
  return bits;
}

Ref<BitMatrix> GridSampler::sampleGrid(Ref<BitMatrix> image, int dimension, float p1ToX, float p1ToY, float p2ToX,
                                       float p2ToY, float p3ToX, float p3ToY, float p4ToX, float p4ToY, float p1FromX, float p1FromY, float p2FromX,
                                       float p2FromY, float p3FromX, float p3FromY, float p4FromX, float p4FromY) {
  Ref<PerspectiveTransform> transform(PerspectiveTransform::quadrilateralToQuadrilateral(p1ToX, p1ToY, p2ToX, p2ToY,
                                      p3ToX, p3ToY, p4ToX, p4ToY, p1FromX, p1FromY, p2FromX, p2FromY, p3FromX, p3FromY, p4FromX, p4FromY));

  return sampleGrid(image, dimension, transform);

}

void GridSampler::checkAndNudgePoints(Ref<BitMatrix> image, vector<float> &points) {
  int width = image->getWidth();
  int height = image->getHeight();


  // The Java code assumes that if the start and end points are in bounds, the rest will also be.
  // However, in some unusual cases points in the middle may also be out of bounds.
  // Since we can't rely on an ArrayIndexOutOfBoundsException like Java, we check every point.

  for (size_t offset = 0; offset < points.size(); offset += 2) {
    int x = (int)points[offset];
    int y = (int)points[offset + 1];
    if (x < -1 || x > width || y < -1 || y > height) {
      ostringstream s;
      s << "Transformed point out of bounds at " << x << "," << y;
      throw ReaderException(s.str().c_str());
    }

    if (x == -1) {
      points[offset] = 0.0f;
    } else if (x == width) {
      points[offset] = float(width - 1);
    }
    if (y == -1) {
      points[offset + 1] = 0.0f;
    } else if (y == height) {
      points[offset + 1] = float(height - 1);
    }
  }

}

GridSampler &GridSampler::getInstance() {
  return gridSampler;
}
}

// file: zxing/common/HybridBinarizer.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  HybridBinarizer.cpp
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

// #include <zxing/common/HybridBinarizer.h>

// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
    
namespace {
  const int BLOCK_SIZE_POWER = 3;
  const int BLOCK_SIZE = 1 << BLOCK_SIZE_POWER; // ...0100...00
  const int BLOCK_SIZE_MASK = BLOCK_SIZE - 1;   // ...0011...11
  const int MINIMUM_DIMENSION = BLOCK_SIZE * 5;
}

HybridBinarizer::HybridBinarizer(Ref<LuminanceSource> source) :
  GlobalHistogramBinarizer(source), matrix_(NULL), cached_row_(NULL) {
}

HybridBinarizer::~HybridBinarizer() {
}


Ref<Binarizer>
HybridBinarizer::createBinarizer(Ref<LuminanceSource> source) {
  return Ref<Binarizer> (new HybridBinarizer(source));
}


/**
 * Calculates the final BitMatrix once for all requests. This could be called once from the
 * constructor instead, but there are some advantages to doing it lazily, such as making
 * profiling easier, and not doing heavy lifting when callers don't expect it.
 */
Ref<BitMatrix> HybridBinarizer::getBlackMatrix() {
  if (matrix_) {
    return matrix_;
  }
  LuminanceSource& source = *getLuminanceSource();
  int width = source.getWidth();
  int height = source.getHeight();
  if (width >= MINIMUM_DIMENSION && height >= MINIMUM_DIMENSION) {
    ArrayRef<char> luminances = source.getMatrix();
    int subWidth = width >> BLOCK_SIZE_POWER;
    if ((width & BLOCK_SIZE_MASK) != 0) {
      subWidth++;
    }
    int subHeight = height >> BLOCK_SIZE_POWER;
    if ((height & BLOCK_SIZE_MASK) != 0) {
      subHeight++;
    }
    ArrayRef<int> blackPoints =
      calculateBlackPoints(luminances, subWidth, subHeight, width, height);

    Ref<BitMatrix> newMatrix (new BitMatrix(width, height));
    calculateThresholdForBlock(luminances,
                               subWidth,
                               subHeight,
                               width,
                               height,
                               blackPoints,
                               newMatrix);
    matrix_ = newMatrix;
  } else {
    // If the image is too small, fall back to the global histogram approach.
    matrix_ = GlobalHistogramBinarizer::getBlackMatrix();
  }
  return matrix_;
}

namespace {
  inline int cap(int value, int min, int max) {
    return value < min ? min : value > max ? max : value;
  }
}

void
HybridBinarizer::calculateThresholdForBlock(ArrayRef<char> luminances,
                                            int subWidth,
                                            int subHeight,
                                            int width,
                                            int height,
                                            ArrayRef<int> blackPoints,
                                            Ref<BitMatrix> const& matrix) {
  for (int y = 0; y < subHeight; y++) {
    int yoffset = y << BLOCK_SIZE_POWER;
    int maxYOffset = height - BLOCK_SIZE;
    if (yoffset > maxYOffset) {
      yoffset = maxYOffset;
    }
    for (int x = 0; x < subWidth; x++) {
      int xoffset = x << BLOCK_SIZE_POWER;
      int maxXOffset = width - BLOCK_SIZE;
      if (xoffset > maxXOffset) {
        xoffset = maxXOffset;
      }
      int left = cap(x, 2, subWidth - 3);
      int top = cap(y, 2, subHeight - 3);
      int sum = 0;
      for (int z = -2; z <= 2; z++) {
        int *blackRow = &blackPoints[(top + z) * subWidth];
        sum += blackRow[left - 2];
        sum += blackRow[left - 1];
        sum += blackRow[left];
        sum += blackRow[left + 1];
        sum += blackRow[left + 2];
      }
      int average = sum / 25;
      thresholdBlock(luminances, xoffset, yoffset, average, width, matrix);
    }
  }
}

void HybridBinarizer::thresholdBlock(ArrayRef<char> luminances,
                                     int xoffset,
                                     int yoffset,
                                     int threshold,
                                     int stride,
                                     Ref<BitMatrix> const& matrix) {
  for (int y = 0, offset = yoffset * stride + xoffset;
       y < BLOCK_SIZE;
       y++,  offset += stride) {
    for (int x = 0; x < BLOCK_SIZE; x++) {
      int pixel = luminances[offset + x] & 0xff;
      if (pixel <= threshold) {
        matrix->set(xoffset + x, yoffset + y);
      }
    }
  }
}

namespace {
  inline int getBlackPointFromNeighbors(ArrayRef<int> blackPoints, int subWidth, int x, int y) {
    return (blackPoints[(y-1)*subWidth+x] +
            2*blackPoints[y*subWidth+x-1] +
            blackPoints[(y-1)*subWidth+x-1]) >> 2;
  }
}


ArrayRef<int> HybridBinarizer::calculateBlackPoints(ArrayRef<char> luminances,
                                                    int subWidth,
                                                    int subHeight,
                                                    int width,
                                                    int height) {
  const int minDynamicRange = 24;

  ArrayRef<int> blackPoints (subHeight * subWidth);
  for (int y = 0; y < subHeight; y++) {
    int yoffset = y << BLOCK_SIZE_POWER;
    int maxYOffset = height - BLOCK_SIZE;
    if (yoffset > maxYOffset) {
      yoffset = maxYOffset;
    }
    for (int x = 0; x < subWidth; x++) {
      int xoffset = x << BLOCK_SIZE_POWER;
      int maxXOffset = width - BLOCK_SIZE;
      if (xoffset > maxXOffset) {
        xoffset = maxXOffset;
      }
      int sum = 0;
      int min = 0xFF;
      int max = 0;
      for (int yy = 0, offset = yoffset * width + xoffset;
           yy < BLOCK_SIZE;
           yy++, offset += width) {
        for (int xx = 0; xx < BLOCK_SIZE; xx++) {
          int pixel = luminances[offset + xx] & 0xFF;
          sum += pixel;
          // still looking for good contrast
          if (pixel < min) {
            min = pixel;
          }
          if (pixel > max) {
            max = pixel;
          }
        }

        // short-circuit min/max tests once dynamic range is met
        if (max - min > minDynamicRange) {
          // finish the rest of the rows quickly
          for (yy++, offset += width; yy < BLOCK_SIZE; yy++, offset += width) {
            for (int xx = 0; xx < BLOCK_SIZE; xx += 2) {
              sum += luminances[offset + xx] & 0xFF;
              sum += luminances[offset + xx + 1] & 0xFF;
            }
          }
        }
      }
      // See
      // http://groups.google.com/group/zxing/browse_thread/thread/d06efa2c35a7ddc0
      int average = sum >> (BLOCK_SIZE_POWER * 2);
      if (max - min <= minDynamicRange) {
        average = min >> 1;
        if (y > 0 && x > 0) {
          int bp = getBlackPointFromNeighbors(blackPoints, subWidth, x, y);
          if (min < bp) {
            average = bp;
          }
        }
      }
      blackPoints[y * subWidth + x] = average;
    }
  }
  return blackPoints;
}
}

// file: zxing/common/IllegalArgumentException.cpp

/*
 *  IllegalArgumentException.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 06/05/2008.
 *  Copyright 2008 Google UK. All rights reserved.
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

// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
    
IllegalArgumentException::IllegalArgumentException() : Exception() {}
IllegalArgumentException::IllegalArgumentException(const char *msg) : Exception(msg) {}
IllegalArgumentException::~IllegalArgumentException() throw() {}
}

// file: zxing/common/PerspectiveTransform.cpp

/*
 *  PerspectiveTransform.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 12/05/2008.
 *  Copyright 2008 Google UK. All rights reserved.
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

// #include <zxing/common/PerspectiveTransform.h>

namespace zxing {
using namespace std;

PerspectiveTransform::PerspectiveTransform(float inA11, float inA21,
                                           float inA31, float inA12,
                                           float inA22, float inA32,
                                           float inA13, float inA23,
                                           float inA33) :
  a11(inA11), a12(inA12), a13(inA13), a21(inA21), a22(inA22), a23(inA23),
  a31(inA31), a32(inA32), a33(inA33) {}

Ref<PerspectiveTransform> PerspectiveTransform::quadrilateralToQuadrilateral(float x0, float y0, float x1, float y1,
    float x2, float y2, float x3, float y3, float x0p, float y0p, float x1p, float y1p, float x2p, float y2p,
    float x3p, float y3p) {
  Ref<PerspectiveTransform> qToS = PerspectiveTransform::quadrilateralToSquare(x0, y0, x1, y1, x2, y2, x3, y3);
  Ref<PerspectiveTransform> sToQ =
    PerspectiveTransform::squareToQuadrilateral(x0p, y0p, x1p, y1p, x2p, y2p, x3p, y3p);
  return sToQ->times(qToS);
}

Ref<PerspectiveTransform> PerspectiveTransform::squareToQuadrilateral(float x0, float y0, float x1, float y1, float x2,
    float y2, float x3, float y3) {
  float dx3 = x0 - x1 + x2 - x3;
  float dy3 = y0 - y1 + y2 - y3;
  if (dx3 == 0.0f && dy3 == 0.0f) {
    Ref<PerspectiveTransform> result(new PerspectiveTransform(x1 - x0, x2 - x1, x0, y1 - y0, y2 - y1, y0, 0.0f,
                                     0.0f, 1.0f));
    return result;
  } else {
    float dx1 = x1 - x2;
    float dx2 = x3 - x2;
    float dy1 = y1 - y2;
    float dy2 = y3 - y2;
    float denominator = dx1 * dy2 - dx2 * dy1;
    float a13 = (dx3 * dy2 - dx2 * dy3) / denominator;
    float a23 = (dx1 * dy3 - dx3 * dy1) / denominator;
    Ref<PerspectiveTransform> result(new PerspectiveTransform(x1 - x0 + a13 * x1, x3 - x0 + a23 * x3, x0, y1 - y0
                                     + a13 * y1, y3 - y0 + a23 * y3, y0, a13, a23, 1.0f));
    return result;
  }
}

Ref<PerspectiveTransform> PerspectiveTransform::quadrilateralToSquare(float x0, float y0, float x1, float y1, float x2,
    float y2, float x3, float y3) {
  // Here, the adjoint serves as the inverse:
  return squareToQuadrilateral(x0, y0, x1, y1, x2, y2, x3, y3)->buildAdjoint();
}

Ref<PerspectiveTransform> PerspectiveTransform::buildAdjoint() {
  // Adjoint is the transpose of the cofactor matrix:
  Ref<PerspectiveTransform> result(new PerspectiveTransform(a22 * a33 - a23 * a32, a23 * a31 - a21 * a33, a21 * a32
                                   - a22 * a31, a13 * a32 - a12 * a33, a11 * a33 - a13 * a31, a12 * a31 - a11 * a32, a12 * a23 - a13 * a22,
                                   a13 * a21 - a11 * a23, a11 * a22 - a12 * a21));
  return result;
}

Ref<PerspectiveTransform> PerspectiveTransform::times(Ref<PerspectiveTransform> other) {
  Ref<PerspectiveTransform> result(new PerspectiveTransform(a11 * other->a11 + a21 * other->a12 + a31 * other->a13,
                                   a11 * other->a21 + a21 * other->a22 + a31 * other->a23, a11 * other->a31 + a21 * other->a32 + a31
                                   * other->a33, a12 * other->a11 + a22 * other->a12 + a32 * other->a13, a12 * other->a21 + a22
                                   * other->a22 + a32 * other->a23, a12 * other->a31 + a22 * other->a32 + a32 * other->a33, a13
                                   * other->a11 + a23 * other->a12 + a33 * other->a13, a13 * other->a21 + a23 * other->a22 + a33
                                   * other->a23, a13 * other->a31 + a23 * other->a32 + a33 * other->a33));
  return result;
}

void PerspectiveTransform::transformPoints(vector<float> &points) {
  int max = (int)points.size();
  for (int i = 0; i < max; i += 2) {
    float x = points[i];
    float y = points[i + 1];
    float denominator = a13 * x + a23 * y + a33;
    points[i] = (a11 * x + a21 * y + a31) / denominator;
    points[i + 1] = (a12 * x + a22 * y + a32) / denominator;
  }
}

ostream& operator<<(ostream& out, const PerspectiveTransform &pt) {
  out << pt.a11 << ", " << pt.a12 << ", " << pt.a13 << ", \n";
  out << pt.a21 << ", " << pt.a22 << ", " << pt.a23 << ", \n";
  out << pt.a31 << ", " << pt.a32 << ", " << pt.a33 << "\n";
  return out;
}

}

// file: zxing/common/Str.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  String.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 20/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/common/Str.h>

namespace zxing {
    
String::String(const std::string &text) :
  text_(text) {
}

String::String(int capacity) {
  text_.reserve(capacity);
}

const std::string& String::getText() const {
  return text_;
}

char String::charAt(int i) const { return text_[i]; }

int String::size() const { return (int)text_.size(); }

int String::length() const { return (int)text_.size(); }

Ref<String> String::substring(int i) const {
  return Ref<String>(new String(text_.substr(i)));
}

void String::append(const std::string &tail) {
  text_.append(tail);
}

void String::append(char c) {
  text_.append(1,c);
}

std::ostream& operator << (std::ostream& out, String const& s) {
  out << s.text_;
  return out;
}
}

// file: zxing/common/StringUtils.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-

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

// #include <zxing/common/StringUtils.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace common {
        
// N.B.: these are the iconv strings for at least some versions of iconv

char const* const StringUtils::PLATFORM_DEFAULT_ENCODING = "UTF-8";
char const* const StringUtils::ASCII = "ASCII";
char const* const StringUtils::SHIFT_JIS = "SHIFT_JIS";
char const* const StringUtils::GB2312 = "GBK";
char const* const StringUtils::EUC_JP = "EUC-JP";
char const* const StringUtils::UTF8 = "UTF-8";
char const* const StringUtils::ISO88591 = "ISO8859-1";
const bool StringUtils::ASSUME_SHIFT_JIS = false;

string
StringUtils::guessEncoding(char* bytes, int length,
                           Hashtable const& hints) {
  Hashtable::const_iterator i = hints.find(DecodeHints::CHARACTER_SET);
  if (i != hints.end()) {
    return i->second;
  }
  typedef bool boolean;
  // For now, merely tries to distinguish ISO-8859-1, UTF-8 and Shift_JIS,
  // which should be by far the most common encodings.
  boolean canBeISO88591 = true;
  boolean canBeShiftJIS = true;
  boolean canBeUTF8 = true;
  int utf8BytesLeft = 0;
  //int utf8LowChars = 0;
  int utf2BytesChars = 0;
  int utf3BytesChars = 0;
  int utf4BytesChars = 0;
  int sjisBytesLeft = 0;
  //int sjisLowChars = 0;
  int sjisKatakanaChars = 0;
  //int sjisDoubleBytesChars = 0;
  int sjisCurKatakanaWordLength = 0;
  int sjisCurDoubleBytesWordLength = 0;
  int sjisMaxKatakanaWordLength = 0;
  int sjisMaxDoubleBytesWordLength = 0;
  //int isoLowChars = 0;
  //int isoHighChars = 0;
  int isoHighOther = 0;

  typedef char byte;
  boolean utf8bom = length > 3 &&
    bytes[0] == (byte) 0xEF &&
    bytes[1] == (byte) 0xBB &&
    bytes[2] == (byte) 0xBF;

  for (int i = 0;
       i < length && (canBeISO88591 || canBeShiftJIS || canBeUTF8);
       i++) {

    int value = bytes[i] & 0xFF;

    // UTF-8 stuff
    if (canBeUTF8) {
      if (utf8BytesLeft > 0) {
        if ((value & 0x80) == 0) {
          canBeUTF8 = false;
        } else {
          utf8BytesLeft--;
        }
      } else if ((value & 0x80) != 0) {
        if ((value & 0x40) == 0) {
          canBeUTF8 = false;
        } else {
          utf8BytesLeft++;
          if ((value & 0x20) == 0) {
            utf2BytesChars++;
          } else {
            utf8BytesLeft++;
            if ((value & 0x10) == 0) {
              utf3BytesChars++;
            } else {
              utf8BytesLeft++;
              if ((value & 0x08) == 0) {
                utf4BytesChars++;
              } else {
                canBeUTF8 = false;
              }
            }
          }
        }
      } //else {
      //utf8LowChars++;
      //}
    }

    // ISO-8859-1 stuff
    if (canBeISO88591) {
      if (value > 0x7F && value < 0xA0) {
        canBeISO88591 = false;
      } else if (value > 0x9F) {
        if (value < 0xC0 || value == 0xD7 || value == 0xF7) {
          isoHighOther++;
        } //else {
        //isoHighChars++;
        //}
      } //else {
      //isoLowChars++;
      //}
    }

    // Shift_JIS stuff
    if (canBeShiftJIS) {
      if (sjisBytesLeft > 0) {
        if (value < 0x40 || value == 0x7F || value > 0xFC) {
          canBeShiftJIS = false;
        } else {
          sjisBytesLeft--;
        }
      } else if (value == 0x80 || value == 0xA0 || value > 0xEF) {
        canBeShiftJIS = false;
      } else if (value > 0xA0 && value < 0xE0) {
        sjisKatakanaChars++;
        sjisCurDoubleBytesWordLength = 0;
        sjisCurKatakanaWordLength++;
        if (sjisCurKatakanaWordLength > sjisMaxKatakanaWordLength) {
          sjisMaxKatakanaWordLength = sjisCurKatakanaWordLength;
        }
      } else if (value > 0x7F) {
        sjisBytesLeft++;
        //sjisDoubleBytesChars++;
        sjisCurKatakanaWordLength = 0;
        sjisCurDoubleBytesWordLength++;
        if (sjisCurDoubleBytesWordLength > sjisMaxDoubleBytesWordLength) {
          sjisMaxDoubleBytesWordLength = sjisCurDoubleBytesWordLength;
        }
      } else {
        //sjisLowChars++;
        sjisCurKatakanaWordLength = 0;
        sjisCurDoubleBytesWordLength = 0;
      }
    }
  }

  if (canBeUTF8 && utf8BytesLeft > 0) {
    canBeUTF8 = false;
  }
  if (canBeShiftJIS && sjisBytesLeft > 0) {
    canBeShiftJIS = false;
  }

  // Easy -- if there is BOM or at least 1 valid not-single byte character (and no evidence it can't be UTF-8), done
  if (canBeUTF8 && (utf8bom || utf2BytesChars + utf3BytesChars + utf4BytesChars > 0)) {
    return UTF8;
  }
  // Easy -- if assuming Shift_JIS or at least 3 valid consecutive not-ascii characters (and no evidence it can't be), done
  if (canBeShiftJIS && (ASSUME_SHIFT_JIS || sjisMaxKatakanaWordLength >= 3 || sjisMaxDoubleBytesWordLength >= 3)) {
    return SHIFT_JIS;
  }
  // Distinguishing Shift_JIS and ISO-8859-1 can be a little tough for short words. The crude heuristic is:
  // - If we saw
  //   - only two consecutive katakana chars in the whole text, or
  //   - at least 10% of bytes that could be "upper" not-alphanumeric Latin1,
  // - then we conclude Shift_JIS, else ISO-8859-1
  if (canBeISO88591 && canBeShiftJIS) {
    return (sjisMaxKatakanaWordLength == 2 && sjisKatakanaChars == 2) || isoHighOther * 10 >= length
      ? SHIFT_JIS : ISO88591;
  }

  // Otherwise, try in order ISO-8859-1, Shift JIS, UTF-8 and fall back to default platform encoding
  if (canBeISO88591) {
    return ISO88591;
  }
  if (canBeShiftJIS) {
    return SHIFT_JIS;
  }
  if (canBeUTF8) {
    return UTF8;
  }
  // Otherwise, we take a wild guess with platform encoding
  return PLATFORM_DEFAULT_ENCODING;
}
}
}

// file: zxing/common/detector/MonochromeRectangleDetector.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  MonochromeRectangleDetector.cpp
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

// #include <zxing/NotFoundException.h>
// #include <zxing/common/detector/MonochromeRectangleDetector.h>
// #include <sstream>
// #include <algorithm>  // vs12, std::min und std:max

namespace zxing {
    
vector<Ref<ResultPoint> > MonochromeRectangleDetector::detect() {
  int height = image_->getHeight();
  int width = image_->getWidth();
  int halfHeight = height >> 1;
  int halfWidth = width >> 1;
  int deltaY = std::max(1, height / (MAX_MODULES << 3));
  int deltaX = std::max(1, width / (MAX_MODULES << 3));

  int top = 0;
  int bottom = height;
  int left = 0;
  int right = width;
  Ref<ResultPoint> pointA(findCornerFromCenter(halfWidth, 0, left, right,
                                               halfHeight, -deltaY, top, bottom, halfWidth >> 1));
  top = (int) pointA->getY() - 1;;
  Ref<ResultPoint> pointB(findCornerFromCenter(halfWidth, -deltaX, left, right,
                                               halfHeight, 0, top, bottom, halfHeight >> 1));
  left = (int) pointB->getX() - 1;
  Ref<ResultPoint> pointC(findCornerFromCenter(halfWidth, deltaX, left, right,
                                               halfHeight, 0, top, bottom, halfHeight >> 1));
  right = (int) pointC->getX() + 1;
  Ref<ResultPoint> pointD(findCornerFromCenter(halfWidth, 0, left, right,
                                               halfHeight, deltaY, top, bottom, halfWidth >> 1));
  bottom = (int) pointD->getY() + 1;

  // Go try to find point A again with better information -- might have been off at first.
  pointA.reset(findCornerFromCenter(halfWidth, 0, left, right,
                                    halfHeight, -deltaY, top, bottom, halfWidth >> 2));

  vector<Ref<ResultPoint> > corners(4);
  corners[0].reset(pointA);
  corners[1].reset(pointB);
  corners[2].reset(pointC);
  corners[3].reset(pointD);
  return corners;
}

Ref<ResultPoint> MonochromeRectangleDetector::findCornerFromCenter(int centerX, int deltaX, int left, int right,
                                                                   int centerY, int deltaY, int top, int bottom, int maxWhiteRun) {
  Ref<TwoInts> lastRange(NULL);
  for (int y = centerY, x = centerX;
       y < bottom && y >= top && x < right && x >= left;
       y += deltaY, x += deltaX) {
    Ref<TwoInts> range(NULL);
    if (deltaX == 0) {
      // horizontal slices, up and down
      range = blackWhiteRange(y, maxWhiteRun, left, right, true);
    } else {
      // vertical slices, left and right
      range = blackWhiteRange(x, maxWhiteRun, top, bottom, false);
    }
    if (range == NULL) {
      if (lastRange == NULL) {
        throw NotFoundException("Couldn't find corners (lastRange = NULL) ");
      } else {
        // lastRange was found
        if (deltaX == 0) {
          int lastY = y - deltaY;
          if (lastRange->start < centerX) {
            if (lastRange->end > centerX) {
              // straddle, choose one or the other based on direction
              Ref<ResultPoint> result(new ResultPoint(deltaY > 0 ? lastRange->start : lastRange->end, lastY));
              return result;
            }
            Ref<ResultPoint> result(new ResultPoint(lastRange->start, lastY));
            return result;
          } else {
            Ref<ResultPoint> result(new ResultPoint(lastRange->end, lastY));
            return result;
          }
        } else {
          int lastX = x - deltaX;
          if (lastRange->start < centerY) {
            if (lastRange->end > centerY) {
              Ref<ResultPoint> result(new ResultPoint(lastX, deltaX < 0 ? lastRange->start : lastRange->end));
              return result;
            }
            Ref<ResultPoint> result(new ResultPoint(lastX, lastRange->start));
            return result;
          } else {
            Ref<ResultPoint> result(new ResultPoint(lastX, lastRange->end));
            return result;
          }
        }
      }
    }
    lastRange = range;
  }
  throw NotFoundException("Couldn't find corners");
}

Ref<TwoInts> MonochromeRectangleDetector::blackWhiteRange(int fixedDimension, int maxWhiteRun, int minDim, int maxDim,
                                                          bool horizontal) {

  int center = (minDim + maxDim) >> 1;

  // Scan left/up first
  int start = center;
  while (start >= minDim) {
    if (horizontal ? image_->get(start, fixedDimension) : image_->get(fixedDimension, start)) {
      start--;
    } else {
      int whiteRunStart = start;
      do {
        start--;
      } while (start >= minDim && !(horizontal ? image_->get(start, fixedDimension) :
                                    image_->get(fixedDimension, start)));
      int whiteRunSize = whiteRunStart - start;
      if (start < minDim || whiteRunSize > maxWhiteRun) {
        start = whiteRunStart;
        break;
      }
    }
  }
  start++;

  // Then try right/down
  int end = center;
  while (end < maxDim) {
    if (horizontal ? image_->get(end, fixedDimension) : image_->get(fixedDimension, end)) {
      end++;
    } else {
      int whiteRunStart = end;
      do {
        end++;
      } while (end < maxDim && !(horizontal ? image_->get(end, fixedDimension) :
                                 image_->get(fixedDimension, end)));
      int whiteRunSize = end - whiteRunStart;
      if (end >= maxDim || whiteRunSize > maxWhiteRun) {
        end = whiteRunStart;
        break;
      }
    }
  }
  end--;
  Ref<TwoInts> result(NULL);
  if (end > start) {
    result = new TwoInts;
    result->start = start;
    result->end = end;
  }
  return result;
}
}

// file: zxing/common/detector/WhiteRectangleDetector.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  WhiteRectangleDetector.cpp
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

// #include <zxing/NotFoundException.h>
// #include <zxing/common/detector/WhiteRectangleDetector.h>
// #include <zxing/common/detector/MathUtils.h>
// #include <sstream>

namespace zxing {
    
int WhiteRectangleDetector::INIT_SIZE = 30;
int WhiteRectangleDetector::CORR = 1;

WhiteRectangleDetector::WhiteRectangleDetector(Ref<BitMatrix> image) : image_(image) {
  width_ = image->getWidth();
  height_ = image->getHeight();

  leftInit_ = (width_ - INIT_SIZE) >> 1;
  rightInit_ = (width_ + INIT_SIZE) >> 1;
  upInit_ = (height_ - INIT_SIZE) >> 1;
  downInit_ = (height_ + INIT_SIZE) >> 1;

  if (upInit_ < 0 || leftInit_ < 0 || downInit_ >= height_ || rightInit_ >= width_) {
    throw NotFoundException("Invalid dimensions WhiteRectangleDetector");
}
}

WhiteRectangleDetector::WhiteRectangleDetector(Ref<BitMatrix> image, int initSize, int x, int y) : image_(image) {
  width_ = image->getWidth();
  height_ = image->getHeight();

  int halfsize = initSize >> 1;
  leftInit_ = x - halfsize;
  rightInit_ = x + halfsize;
  upInit_ = y - halfsize;
  downInit_ = y + halfsize;

  if (upInit_ < 0 || leftInit_ < 0 || downInit_ >= height_ || rightInit_ >= width_) {
    throw NotFoundException("Invalid dimensions WhiteRectangleDetector");
  }
}

/**
 * <p>
 * Detects a candidate barcode-like rectangular region within an image. It
 * starts around the center of the image, increases the size of the candidate
 * region until it finds a white rectangular region.
 * </p>
 *
 * @return {@link vector<Ref<ResultPoint> >} describing the corners of the rectangular
 *         region. The first and last points are opposed on the diagonal, as
 *         are the second and third. The first point will be the topmost
 *         point and the last, the bottommost. The second point will be
 *         leftmost and the third, the rightmost
 * @throws NotFoundException if no Data Matrix Code can be found
*/
std::vector<Ref<ResultPoint> > WhiteRectangleDetector::detect() {
  int left = leftInit_;
  int right = rightInit_;
  int up = upInit_;
  int down = downInit_;

  bool sizeExceeded = false;
  bool aBlackPointFoundOnBorder = true;
  bool atLeastOneBlackPointFoundOnBorder = false;

  while (aBlackPointFoundOnBorder) {
    aBlackPointFoundOnBorder = false;

    // .....
    // .   |
    // .....
    bool rightBorderNotWhite = true;
    while (rightBorderNotWhite && right < width_) {
      rightBorderNotWhite = containsBlackPoint(up, down, right, false);
      if (rightBorderNotWhite) {
        right++;
        aBlackPointFoundOnBorder = true;
      }
    }

    if (right >= width_) {
      sizeExceeded = true;
      break;
    }

    // .....
    // .   .
    // .___.
    bool bottomBorderNotWhite = true;
    while (bottomBorderNotWhite && down < height_) {
      bottomBorderNotWhite = containsBlackPoint(left, right, down, true);
      if (bottomBorderNotWhite) {
        down++;
        aBlackPointFoundOnBorder = true;
      }
    }

    if (down >= height_) {
      sizeExceeded = true;
      break;
    }

    // .....
    // |   .
    // .....
    bool leftBorderNotWhite = true;
    while (leftBorderNotWhite && left >= 0) {
      leftBorderNotWhite = containsBlackPoint(up, down, left, false);
      if (leftBorderNotWhite) {
        left--;
        aBlackPointFoundOnBorder = true;
      }
    }

    if (left < 0) {
      sizeExceeded = true;
      break;
    }

    // .___.
    // .   .
    // .....
    bool topBorderNotWhite = true;
    while (topBorderNotWhite && up >= 0) {
      topBorderNotWhite = containsBlackPoint(left, right, up, true);
      if (topBorderNotWhite) {
        up--;
        aBlackPointFoundOnBorder = true;
      }
    }

    if (up < 0) {
      sizeExceeded = true;
      break;
    }

    if (aBlackPointFoundOnBorder) {
      atLeastOneBlackPointFoundOnBorder = true;
    }

  }
  if (!sizeExceeded && atLeastOneBlackPointFoundOnBorder) {

    int maxSize = right - left;

    Ref<ResultPoint> z(NULL);
    //go up right
    for (int i = 1; i < maxSize; i++) {
      z = getBlackPointOnSegment(left, down - i, left + i, down);
      if (z != NULL) {
        break;
      }
    }

    if (z == NULL) {
      throw NotFoundException("z == NULL");
    }

    Ref<ResultPoint> t(NULL);
    //go down right
    for (int i = 1; i < maxSize; i++) {
      t = getBlackPointOnSegment(left, up + i, left + i, up);
      if (t != NULL) {
        break;
      }
    }

    if (t == NULL) {
      throw NotFoundException("t == NULL");
    }

    Ref<ResultPoint> x(NULL);
    //go down left
    for (int i = 1; i < maxSize; i++) {
      x = getBlackPointOnSegment(right, up + i, right - i, up);
      if (x != NULL) {
        break;
      }
    }

    if (x == NULL) {
      throw NotFoundException("x == NULL");
    }

    Ref<ResultPoint> y(NULL);
    //go up left
    for (int i = 1; i < maxSize; i++) {
      y = getBlackPointOnSegment(right, down - i, right - i, down);
      if (y != NULL) {
        break;
      }
    }

    if (y == NULL) {
      throw NotFoundException("y == NULL");
    }

    return centerEdges(y, z, x, t);

  } else {
    throw NotFoundException("No black point found on border");
  }
}

Ref<ResultPoint>
WhiteRectangleDetector::getBlackPointOnSegment(int aX_, int aY_, int bX_, int bY_) {
  float aX = float(aX_), aY = float(aY_), bX = float(bX_), bY = float(bY_);
  int dist = MathUtils::round(MathUtils::distance(aX, aY, bX, bY));
  float xStep = (bX - aX) / dist;
  float yStep = (bY - aY) / dist;

  for (int i = 0; i < dist; i++) {
    int x = MathUtils::round(aX + i * xStep);
    int y = MathUtils::round(aY + i * yStep);
    if (image_->get(x, y)) {
      Ref<ResultPoint> point(new ResultPoint(float(x), float(y)));
      return point;
    }
  }
  Ref<ResultPoint> point(NULL);
  return point;
}

/**
 * recenters the points of a constant distance towards the center
 *
 * @param y bottom most point
 * @param z left most point
 * @param x right most point
 * @param t top most point
 * @return {@link vector<Ref<ResultPoint> >} describing the corners of the rectangular
 *         region. The first and last points are opposed on the diagonal, as
 *         are the second and third. The first point will be the topmost
 *         point and the last, the bottommost. The second point will be
 *         leftmost and the third, the rightmost
 */
vector<Ref<ResultPoint> > WhiteRectangleDetector::centerEdges(Ref<ResultPoint> y, Ref<ResultPoint> z,
                                  Ref<ResultPoint> x, Ref<ResultPoint> t) {

  //
  //       t            t
  //  z                      x
  //        x    OR    z
  //   y                    y
  //

  float yi = y->getX();
  float yj = y->getY();
  float zi = z->getX();
  float zj = z->getY();
  float xi = x->getX();
  float xj = x->getY();
  float ti = t->getX();
  float tj = t->getY();

  std::vector<Ref<ResultPoint> > corners(4);
  if (yi < (float)width_/2.0f) {
    Ref<ResultPoint> pointA(new ResultPoint(ti - CORR, tj + CORR));
    Ref<ResultPoint> pointB(new ResultPoint(zi + CORR, zj + CORR));
    Ref<ResultPoint> pointC(new ResultPoint(xi - CORR, xj - CORR));
    Ref<ResultPoint> pointD(new ResultPoint(yi + CORR, yj - CORR));
	  corners[0].reset(pointA);
	  corners[1].reset(pointB);
	  corners[2].reset(pointC);
	  corners[3].reset(pointD);
  } else {
    Ref<ResultPoint> pointA(new ResultPoint(ti + CORR, tj + CORR));
    Ref<ResultPoint> pointB(new ResultPoint(zi + CORR, zj - CORR));
    Ref<ResultPoint> pointC(new ResultPoint(xi - CORR, xj + CORR));
    Ref<ResultPoint> pointD(new ResultPoint(yi - CORR, yj - CORR));
	  corners[0].reset(pointA);
	  corners[1].reset(pointB);
	  corners[2].reset(pointC);
	  corners[3].reset(pointD);
  }
  return corners;
}

/**
 * Determines whether a segment contains a black point
 *
 * @param a          min value of the scanned coordinate
 * @param b          max value of the scanned coordinate
 * @param fixed      value of fixed coordinate
 * @param horizontal set to true if scan must be horizontal, false if vertical
 * @return true if a black point has been found, else false.
 */
bool WhiteRectangleDetector::containsBlackPoint(int a, int b, int fixed, bool horizontal) {
  if (horizontal) {
    for (int x = a; x <= b; x++) {
      if (image_->get(x, fixed)) {
        return true;
      }
    }
  } else {
    for (int y = a; y <= b; y++) {
      if (image_->get(fixed, y)) {
        return true;
      }
    }
  }

  return false;
}
}

// file: zxing/common/reedsolomon/GenericGF.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  GenericGF.cpp
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

// #include <iostream>
// #include <zxing/common/reedsolomon/GenericGF.h>
// #include <zxing/common/reedsolomon/GenericGFPoly.h>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
    
Ref<GenericGF> GenericGF::AZTEC_DATA_12(new GenericGF(0x1069, 4096, 1));
Ref<GenericGF> GenericGF::AZTEC_DATA_10(new GenericGF(0x409, 1024, 1));
Ref<GenericGF> GenericGF::AZTEC_DATA_6(new GenericGF(0x43, 64, 1));
Ref<GenericGF> GenericGF::AZTEC_PARAM(new GenericGF(0x13, 16, 1));
Ref<GenericGF> GenericGF::QR_CODE_FIELD_256(new GenericGF(0x011D, 256, 0));
Ref<GenericGF> GenericGF::DATA_MATRIX_FIELD_256(new GenericGF(0x012D, 256, 1));
Ref<GenericGF> GenericGF::AZTEC_DATA_8 = DATA_MATRIX_FIELD_256;
Ref<GenericGF> GenericGF::MAXICODE_FIELD_64 = AZTEC_DATA_6;

namespace {
  int INITIALIZATION_THRESHOLD = 0;
}

GenericGF::GenericGF(int primitive_, int size_, int b)
  : size(size_), primitive(primitive_), generatorBase(b), initialized(false) {
  if (size <= INITIALIZATION_THRESHOLD) {
    initialize();
  }
}

void GenericGF::initialize() {
  expTable.resize(size);
  logTable.resize(size);

  int x = 1;

  for (int i = 0; i < size; i++) {
    expTable[i] = x;
    x <<= 1; // x = x * 2; we're assuming the generator alpha is 2
    if (x >= size) {
      x ^= primitive;
      x &= size-1;
    }
  }
  for (int i = 0; i < size-1; i++) {
    logTable[expTable[i]] = i;
  }
  //logTable[0] == 0 but this should never be used
  zero =
    Ref<GenericGFPoly>(new GenericGFPoly(*this, ArrayRef<int>(new Array<int>(1))));
  zero->getCoefficients()[0] = 0;
  one =
    Ref<GenericGFPoly>(new GenericGFPoly(*this, ArrayRef<int>(new Array<int>(1))));
  one->getCoefficients()[0] = 1;
  initialized = true;
}

void GenericGF::checkInit() {
  if (!initialized) {
    initialize();
  }
}

Ref<GenericGFPoly> GenericGF::getZero() {
  checkInit();
  return zero;
}

Ref<GenericGFPoly> GenericGF::getOne() {
  checkInit();
  return one;
}

Ref<GenericGFPoly> GenericGF::buildMonomial(int degree, int coefficient) {
  checkInit();

  if (degree < 0) {
    throw IllegalArgumentException("Degree must be non-negative");
  }
  if (coefficient == 0) {
    return zero;
  }
  ArrayRef<int> coefficients(new Array<int>(degree + 1));
  coefficients[0] = coefficient;

  return Ref<GenericGFPoly>(new GenericGFPoly(*this, coefficients));
}

int GenericGF::addOrSubtract(int a, int b) {
  return a ^ b;
}

int GenericGF::exp(int a) {
  checkInit();
  return expTable[a];
}

int GenericGF::log(int a) {
  checkInit();
  if (a == 0) {
    throw IllegalArgumentException("cannot give log(0)");
  }
  return logTable[a];
}

int GenericGF::inverse(int a) {
  checkInit();
  if (a == 0) {
    throw IllegalArgumentException("Cannot calculate the inverse of 0");
  }
  return expTable[size - logTable[a] - 1];
}

int GenericGF::multiply(int a, int b) {
  checkInit();

  if (a == 0 || b == 0) {
    return 0;
  }

  return expTable[(logTable[a] + logTable[b]) % (size - 1)];
  }

int GenericGF::getSize() {
  return size;
}

int GenericGF::getGeneratorBase() {
  return generatorBase;
}
}

// file: zxing/common/reedsolomon/GenericGFPoly.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  GenericGFPoly.cpp
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

// #include <iostream>
// #include <zxing/common/reedsolomon/GenericGFPoly.h>
// #include <zxing/common/reedsolomon/GenericGF.h>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
    
GenericGFPoly::GenericGFPoly(GenericGF &field,
                             ArrayRef<int> coefficients)
  :  field_(field) {
  if (coefficients->size() == 0) {
    throw IllegalArgumentException("need coefficients");
  }
  int coefficientsLength = (int)coefficients->size();
  if (coefficientsLength > 1 && coefficients[0] == 0) {
    // Leading term must be non-zero for anything except the constant polynomial "0"
    int firstNonZero = 1;
    while (firstNonZero < coefficientsLength && coefficients[firstNonZero] == 0) {
      firstNonZero++;
    }
    if (firstNonZero == coefficientsLength) {
      coefficients_ = field.getZero()->getCoefficients();
    } else {
      coefficients_ = ArrayRef<int>(new Array<int>(coefficientsLength-firstNonZero));
      for (int i = 0; i < (int)coefficients_->size(); i++) {
        coefficients_[i] = coefficients[i + firstNonZero];
      }
    }
  } else {
    coefficients_ = coefficients;
  }
}

ArrayRef<int> GenericGFPoly::getCoefficients() {
  return coefficients_;
}

int GenericGFPoly::getDegree() {
  return (int)coefficients_->size() - 1;
}

bool GenericGFPoly::isZero() {
  return coefficients_[0] == 0;
}

int GenericGFPoly::getCoefficient(int degree) {
  return coefficients_[(int)coefficients_->size() - 1 - degree];
}

int GenericGFPoly::evaluateAt(int a) {
  if (a == 0) {
    // Just return the x^0 coefficient
    return getCoefficient(0);
  }

  int size = (int)coefficients_->size();
  if (a == 1) {
    // Just the sum of the coefficients
    int result = 0;
    for (int i = 0; i < size; i++) {
      result = GenericGF::addOrSubtract(result, coefficients_[i]);
    }
    return result;
  }
  int result = coefficients_[0];
  for (int i = 1; i < size; i++) {
    result = GenericGF::addOrSubtract(field_.multiply(a, result), coefficients_[i]);
  }
  return result;
}

Ref<GenericGFPoly> GenericGFPoly::addOrSubtract(Ref<zxing::GenericGFPoly> other) {
  if (!(&field_ == &other->field_)) {
    throw IllegalArgumentException("GenericGFPolys do not have same GenericGF field");
  }
  if (isZero()) {
    return other;
  }
  if (other->isZero()) {
    return Ref<GenericGFPoly>(this);
  }

  ArrayRef<int> smallerCoefficients = coefficients_;
  ArrayRef<int> largerCoefficients = other->getCoefficients();
  if (smallerCoefficients->size() > largerCoefficients->size()) {
    ArrayRef<int> temp = smallerCoefficients;
    smallerCoefficients = largerCoefficients;
    largerCoefficients = temp;
  }

  ArrayRef<int> sumDiff(new Array<int>((int)largerCoefficients->size()));
  int lengthDiff = (int)(largerCoefficients->size() - smallerCoefficients->size());
  // Copy high-order terms only found in higher-degree polynomial's coefficients
  for (int i = 0; i < lengthDiff; i++) {
    sumDiff[i] = largerCoefficients[i];
  }

  for (int i = lengthDiff; i < (int)largerCoefficients->size(); i++) {
    sumDiff[i] = GenericGF::addOrSubtract(smallerCoefficients[i-lengthDiff],
                                          largerCoefficients[i]);
  }

  return Ref<GenericGFPoly>(new GenericGFPoly(field_, sumDiff));
}

Ref<GenericGFPoly> GenericGFPoly::multiply(Ref<zxing::GenericGFPoly> other) {
  if (!(&field_ == &other->field_)) {
    throw IllegalArgumentException("GenericGFPolys do not have same GenericGF field");
  }

  if (isZero() || other->isZero()) {
    return field_.getZero();
  }

  ArrayRef<int> aCoefficients = coefficients_;
  size_t aLength = aCoefficients->size();

  ArrayRef<int> bCoefficients = other->getCoefficients();
  size_t bLength = bCoefficients->size();

  ArrayRef<int> product(new Array<int>((int)(aLength + bLength) - 1));
  for (int i = 0; i < aLength; i++) {
    int aCoeff = aCoefficients[i];
    for (int j = 0; j < bLength; j++) {
      product[i+j] = GenericGF::addOrSubtract(product[i+j],
                                              field_.multiply(aCoeff, bCoefficients[j]));
    }
  }

  return Ref<GenericGFPoly>(new GenericGFPoly(field_, product));
}

Ref<GenericGFPoly> GenericGFPoly::multiply(int scalar) {
  if (scalar == 0) {
    return field_.getZero();
  }
  if (scalar == 1) {
    return Ref<GenericGFPoly>(this);
  }
  int size = (int)coefficients_->size();
  ArrayRef<int> product(new Array<int>(size));
  for (int i = 0; i < size; i++) {
    product[i] = field_.multiply(coefficients_[i], scalar);
  }
  return Ref<GenericGFPoly>(new GenericGFPoly(field_, product));
}

Ref<GenericGFPoly> GenericGFPoly::multiplyByMonomial(int degree, int coefficient) {
  if (degree < 0) {
    throw IllegalArgumentException("degree must not be less then 0");
  }
  if (coefficient == 0) {
    return field_.getZero();
  }
  int size = (int)coefficients_->size();
  ArrayRef<int> product(new Array<int>(size+degree));
  for (int i = 0; i < size; i++) {
    product[i] = field_.multiply(coefficients_[i], coefficient);
  }
  return Ref<GenericGFPoly>(new GenericGFPoly(field_, product));
}

std::vector<Ref<GenericGFPoly> > GenericGFPoly::divide(Ref<GenericGFPoly> other) {
  if (!(&field_ == &other->field_)) {
    throw IllegalArgumentException("GenericGFPolys do not have same GenericGF field");
  }
  if (other->isZero()) {
    throw IllegalArgumentException("divide by 0");
  }

  Ref<GenericGFPoly> quotient = field_.getZero();
  Ref<GenericGFPoly> remainder = Ref<GenericGFPoly>(this);

  int denominatorLeadingTerm = other->getCoefficient(other->getDegree());
  int inverseDenominatorLeadingTerm = field_.inverse(denominatorLeadingTerm);

  while (remainder->getDegree() >= other->getDegree() && !remainder->isZero()) {
    int degreeDifference = remainder->getDegree() - other->getDegree();
    int scale = field_.multiply(remainder->getCoefficient(remainder->getDegree()),
                                inverseDenominatorLeadingTerm);
    Ref<GenericGFPoly> term = other->multiplyByMonomial(degreeDifference, scale);
    Ref<GenericGFPoly> iterationQuotiont = field_.buildMonomial(degreeDifference,
                                                                scale);
    quotient = quotient->addOrSubtract(iterationQuotiont);
    remainder = remainder->addOrSubtract(term);
  }

  std::vector<Ref<GenericGFPoly> > returnValue(2);
  returnValue[0] = quotient;
  returnValue[1] = remainder;
  return returnValue;
}
}

// file: zxing/common/reedsolomon/ReedSolomonDecoder.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Created by Christian Brunschen on 05/05/2008.
 *  Copyright 2008 Google UK. All rights reserved.
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

// #include <memory>
// #include <zxing/common/reedsolomon/ReedSolomonDecoder.h>
// #include <zxing/common/reedsolomon/ReedSolomonException.h>
// #include <zxing/common/IllegalArgumentException.h>
// #include <zxing/IllegalStateException.h>

namespace zxing {
    
ReedSolomonDecoder::ReedSolomonDecoder(Ref<GenericGF> field_) : field(field_) {}

ReedSolomonDecoder::~ReedSolomonDecoder() {
}

void ReedSolomonDecoder::decode(ArrayRef<int> received, int twoS) {
  Ref<GenericGFPoly> poly(new GenericGFPoly(*field, received));
  ArrayRef<int> syndromeCoefficients(twoS);
  bool noError = true;
  for (int i = 0; i < twoS; i++) {
    int eval = poly->evaluateAt(field->exp(i + field->getGeneratorBase()));
    syndromeCoefficients[(int)syndromeCoefficients->size() - 1 - i] = eval;
    if (eval != 0) {
      noError = false;
    }
  }
  if (noError) {
    return;
  }
  Ref<GenericGFPoly> syndrome(new GenericGFPoly(*field, syndromeCoefficients));
  vector<Ref<GenericGFPoly> > sigmaOmega =
    runEuclideanAlgorithm(field->buildMonomial(twoS, 1), syndrome, twoS);
  Ref<GenericGFPoly> sigma = sigmaOmega[0];
  Ref<GenericGFPoly> omega = sigmaOmega[1];
  ArrayRef<int> errorLocations = findErrorLocations(sigma);
  ArrayRef<int> errorMagitudes = findErrorMagnitudes(omega, errorLocations);
  for (int i = 0; i < errorLocations->size(); i++) {
    int position = (int)received->size() - 1 - field->log(errorLocations[i]);
    if (position < 0) {
      throw ReedSolomonException("Bad error location");
    }
    received[position] = GenericGF::addOrSubtract(received[position], errorMagitudes[i]);
  }
}

vector<Ref<GenericGFPoly> > ReedSolomonDecoder::runEuclideanAlgorithm(Ref<GenericGFPoly> a,
                                                                      Ref<GenericGFPoly> b,
                                                                      int R) {
  // Assume a's degree is >= b's
  if (a->getDegree() < b->getDegree()) {
    Ref<GenericGFPoly> tmp = a;
    a = b;
    b = tmp;
  }

  Ref<GenericGFPoly> rLast(a);
  Ref<GenericGFPoly> r(b);
  Ref<GenericGFPoly> tLast(field->getZero());
  Ref<GenericGFPoly> t(field->getOne());

  // Run Euclidean algorithm until r's degree is less than R/2
  while (r->getDegree() >= R / 2) {
    Ref<GenericGFPoly> rLastLast(rLast);
    Ref<GenericGFPoly> tLastLast(tLast);
    rLast = r;
    tLast = t;

    // Divide rLastLast by rLast, with quotient q and remainder r
    if (rLast->isZero()) {
      // Oops, Euclidean algorithm already terminated?
      throw ReedSolomonException("r_{i-1} was zero");
    }
    r = rLastLast;
    Ref<GenericGFPoly> q = field->getZero();
    int denominatorLeadingTerm = rLast->getCoefficient(rLast->getDegree());
    int dltInverse = field->inverse(denominatorLeadingTerm);
    while (r->getDegree() >= rLast->getDegree() && !r->isZero()) {
      int degreeDiff = r->getDegree() - rLast->getDegree();
      int scale = field->multiply(r->getCoefficient(r->getDegree()), dltInverse);
      q = q->addOrSubtract(field->buildMonomial(degreeDiff, scale));
      r = r->addOrSubtract(rLast->multiplyByMonomial(degreeDiff, scale));
    }

    t = q->multiply(tLast)->addOrSubtract(tLastLast);

    if (r->getDegree() >= rLast->getDegree()) {
      throw IllegalStateException("Division algorithm failed to reduce polynomial?");
    }
  }

  int sigmaTildeAtZero = t->getCoefficient(0);
  if (sigmaTildeAtZero == 0) {
    throw ReedSolomonException("sigmaTilde(0) was zero");
  }

  int inverse = field->inverse(sigmaTildeAtZero);
  Ref<GenericGFPoly> sigma(t->multiply(inverse));
  Ref<GenericGFPoly> omega(r->multiply(inverse));
  vector<Ref<GenericGFPoly> > result(2);
  result[0] = sigma;
  result[1] = omega;
  return result;
}

ArrayRef<int> ReedSolomonDecoder::findErrorLocations(Ref<GenericGFPoly> errorLocator) {
  // This is a direct application of Chien's search
  int numErrors = errorLocator->getDegree();
  if (numErrors == 1) { // shortcut
    ArrayRef<int> result(new Array<int>(1));
    result[0] = errorLocator->getCoefficient(1);
    return result;
  }
  ArrayRef<int> result(new Array<int>(numErrors));
  int e = 0;
  for (int i = 1; i < field->getSize() && e < numErrors; i++) {
    if (errorLocator->evaluateAt(i) == 0) {
      result[e] = field->inverse(i);
      e++;
    }
  }
  if (e != numErrors) {
    throw ReedSolomonException("Error locator degree does not match number of roots");
  }
  return result;
}

ArrayRef<int> ReedSolomonDecoder::findErrorMagnitudes(Ref<GenericGFPoly> errorEvaluator, ArrayRef<int> errorLocations) {
  // This is directly applying Forney's Formula
  int s = (int)errorLocations->size();
  ArrayRef<int> result(new Array<int>(s));
  for (int i = 0; i < s; i++) {
    int xiInverse = field->inverse(errorLocations[i]);
    int denominator = 1;
    for (int j = 0; j < s; j++) {
      if (i != j) {
        int term = field->multiply(errorLocations[j], xiInverse);
        int termPlus1 = (term & 0x1) == 0 ? term | 1 : term & ~1;
        denominator = field->multiply(denominator, termPlus1);
      }
    }
    result[i] = field->multiply(errorEvaluator->evaluateAt(xiInverse),
                                field->inverse(denominator));
    if (field->getGeneratorBase() != 0) {
      result[i] = field->multiply(result[i], xiInverse);
    }
  }
  return result;
}
}

// file: zxing/common/reedsolomon/ReedSolomonException.cpp

/*
 *  ReedSolomonException.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 06/05/2008.
 *  Copyright 2008 Google UK. All rights reserved.
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

// #include <zxing/common/reedsolomon/ReedSolomonException.h>

namespace zxing {
ReedSolomonException::ReedSolomonException(const char *msg) throw() :
    Exception(msg) {
}
ReedSolomonException::~ReedSolomonException() throw() {
}

}

// file: zxing/datamatrix/DataMatrixReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  DataMatrixReader.cpp
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

// #include <zxing/datamatrix/DataMatrixReader.h>
// #include <zxing/datamatrix/detector/Detector.h>
// #include <iostream>

namespace zxing {
namespace datamatrix {

using namespace std;

DataMatrixReader::DataMatrixReader() :
    decoder_() {
}

Ref<Result> DataMatrixReader::decode(Ref<BinaryBitmap> image, DecodeHints hints) {
  (void)hints;
  Detector detector(image->getBlackMatrix());
  Ref<DetectorResult> detectorResult(detector.detect());
  ArrayRef< Ref<ResultPoint> > points(detectorResult->getPoints());


  Ref<DecoderResult> decoderResult(decoder_.decode(detectorResult->getBits()));

  Ref<Result> result(
    new Result(decoderResult->getText(), decoderResult->getRawBytes(), points, BarcodeFormat::DATA_MATRIX));

  return result;
}

DataMatrixReader::~DataMatrixReader() {
}

}
}

// file: zxing/datamatrix/Version.cpp

/*
 *  Version.cpp
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

// #include <zxing/datamatrix/Version.h>
// #include <limits>
// #include <iostream>

namespace zxing {
namespace datamatrix {
using namespace std;

ECB::ECB(int count, int dataCodewords) :
    count_(count), dataCodewords_(dataCodewords) {
}

int ECB::getCount() {
  return count_;
}

int ECB::getDataCodewords() {
  return dataCodewords_;
}

ECBlocks::ECBlocks(int ecCodewords, ECB *ecBlocks) :
    ecCodewords_(ecCodewords), ecBlocks_(1, ecBlocks) {
}

ECBlocks::ECBlocks(int ecCodewords, ECB *ecBlocks1, ECB *ecBlocks2) :
    ecCodewords_(ecCodewords), ecBlocks_(1, ecBlocks1) {
  ecBlocks_.push_back(ecBlocks2);
}

int ECBlocks::getECCodewords() {
  return ecCodewords_;
}

std::vector<ECB*>& ECBlocks::getECBlocks() {
  return ecBlocks_;
}

ECBlocks::~ECBlocks() {
  for (size_t i = 0; i < ecBlocks_.size(); i++) {
    delete ecBlocks_[i];
  }
}

vector<Ref<Version> > Version::VERSIONS;
static int N_VERSIONS = Version::buildVersions();

Version::Version(int versionNumber, int symbolSizeRows, int symbolSizeColumns, int dataRegionSizeRows,
		int dataRegionSizeColumns, ECBlocks* ecBlocks) : versionNumber_(versionNumber),
		symbolSizeRows_(symbolSizeRows), symbolSizeColumns_(symbolSizeColumns),
		dataRegionSizeRows_(dataRegionSizeRows), dataRegionSizeColumns_(dataRegionSizeColumns),
		ecBlocks_(ecBlocks), totalCodewords_(0) {
    // Calculate the total number of codewords
    int total = 0;
    int ecCodewords = ecBlocks_->getECCodewords();
    vector<ECB*> &ecbArray = ecBlocks_->getECBlocks();
    for (unsigned int i = 0; i < ecbArray.size(); i++) {
      ECB *ecBlock = ecbArray[i];
      total += ecBlock->getCount() * (ecBlock->getDataCodewords() + ecCodewords);
    }
    totalCodewords_ = total;
}

Version::~Version() {
    delete ecBlocks_;
}

int Version::getVersionNumber() {
  return versionNumber_;
}

int Version::getSymbolSizeRows() {
  return symbolSizeRows_;
}

int Version::getSymbolSizeColumns() {
  return symbolSizeColumns_;
}

int Version::getDataRegionSizeRows() {
  return dataRegionSizeRows_;
}

int Version::getDataRegionSizeColumns() {
  return dataRegionSizeColumns_;
}

int Version::getTotalCodewords() {
  return totalCodewords_;
}

ECBlocks* Version::getECBlocks() {
  return ecBlocks_;
}

Ref<Version> Version::getVersionForDimensions(int numRows, int numColumns) {
    if ((numRows & 0x01) != 0 || (numColumns & 0x01) != 0) {
      throw ReaderException("Number of rows and columns must be even");
    }

    // TODO(bbrown): This is doing a linear search through the array of versions.
    // If we interleave the rectangular versions with the square versions we could
    // do a binary search.
    for (int i = 0; i < N_VERSIONS; ++i){
      Ref<Version> version(VERSIONS[i]);
      if (version->getSymbolSizeRows() == numRows && version->getSymbolSizeColumns() == numColumns) {
        return version;
      }
    }
    throw ReaderException("Error version not found");
  }

/**
 * See ISO 16022:2006 5.5.1 Table 7
 */
int Version::buildVersions() {
  VERSIONS.push_back(Ref<Version>(new Version(1, 10, 10, 8, 8,
            					  new ECBlocks(5, new ECB(1, 3)))));
  VERSIONS.push_back(Ref<Version>(new Version(2, 12, 12, 10, 10,
            					  new ECBlocks(7, new ECB(1, 5)))));
  VERSIONS.push_back(Ref<Version>(new Version(3, 14, 14, 12, 12,
            					  new ECBlocks(10, new ECB(1, 8)))));
  VERSIONS.push_back(Ref<Version>(new Version(4, 16, 16, 14, 14,
            					  new ECBlocks(12, new ECB(1, 12)))));
  VERSIONS.push_back(Ref<Version>(new Version(5, 18, 18, 16, 16,
            					  new ECBlocks(14, new ECB(1, 18)))));
  VERSIONS.push_back(Ref<Version>(new Version(6, 20, 20, 18, 18,
            					  new ECBlocks(18, new ECB(1, 22)))));
  VERSIONS.push_back(Ref<Version>(new Version(7, 22, 22, 20, 20,
            					  new ECBlocks(20, new ECB(1, 30)))));
  VERSIONS.push_back(Ref<Version>(new Version(8, 24, 24, 22, 22,
            					  new ECBlocks(24, new ECB(1, 36)))));
  VERSIONS.push_back(Ref<Version>(new Version(9, 26, 26, 24, 24,
            					  new ECBlocks(28, new ECB(1, 44)))));
  VERSIONS.push_back(Ref<Version>(new Version(10, 32, 32, 14, 14,
            					  new ECBlocks(36, new ECB(1, 62)))));
  VERSIONS.push_back(Ref<Version>(new Version(11, 36, 36, 16, 16,
            					  new ECBlocks(42, new ECB(1, 86)))));
  VERSIONS.push_back(Ref<Version>(new Version(12, 40, 40, 18, 18,
            					  new ECBlocks(48, new ECB(1, 114)))));
  VERSIONS.push_back(Ref<Version>(new Version(13, 44, 44, 20, 20,
            					  new ECBlocks(56, new ECB(1, 144)))));
  VERSIONS.push_back(Ref<Version>(new Version(14, 48, 48, 22, 22,
            					  new ECBlocks(68, new ECB(1, 174)))));
  VERSIONS.push_back(Ref<Version>(new Version(15, 52, 52, 24, 24,
            					  new ECBlocks(42, new ECB(2, 102)))));
  VERSIONS.push_back(Ref<Version>(new Version(16, 64, 64, 14, 14,
            					  new ECBlocks(56, new ECB(2, 140)))));
  VERSIONS.push_back(Ref<Version>(new Version(17, 72, 72, 16, 16,
            					  new ECBlocks(36, new ECB(4, 92)))));
  VERSIONS.push_back(Ref<Version>(new  Version(18, 80, 80, 18, 18,
            					  new ECBlocks(48, new ECB(4, 114)))));
  VERSIONS.push_back(Ref<Version>(new Version(19, 88, 88, 20, 20,
            					  new ECBlocks(56, new ECB(4, 144)))));
  VERSIONS.push_back(Ref<Version>(new Version(20, 96, 96, 22, 22,
            					  new ECBlocks(68, new ECB(4, 174)))));
  VERSIONS.push_back(Ref<Version>(new Version(21, 104, 104, 24, 24,
            					  new ECBlocks(56, new ECB(6, 136)))));
  VERSIONS.push_back(Ref<Version>(new Version(22, 120, 120, 18, 18,
            					  new ECBlocks(68, new ECB(6, 175)))));
  VERSIONS.push_back(Ref<Version>(new Version(23, 132, 132, 20, 20,
            					  new ECBlocks(62, new ECB(8, 163)))));
  VERSIONS.push_back(Ref<Version>(new Version(24, 144, 144, 22, 22,
            					  new ECBlocks(62, new ECB(8, 156), new ECB(2, 155)))));
  VERSIONS.push_back(Ref<Version>(new Version(25, 8, 18, 6, 16,
            					  new ECBlocks(7, new ECB(1, 5)))));
  VERSIONS.push_back(Ref<Version>(new Version(26, 8, 32, 6, 14,
            					  new ECBlocks(11, new ECB(1, 10)))));
  VERSIONS.push_back(Ref<Version>(new Version(27, 12, 26, 10, 24,
					              new ECBlocks(14, new ECB(1, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(28, 12, 36, 10, 16,
					              new ECBlocks(18, new ECB(1, 22)))));
  VERSIONS.push_back(Ref<Version>(new Version(29, 16, 36, 14, 16,
					              new ECBlocks(24, new ECB(1, 32)))));
  VERSIONS.push_back(Ref<Version>(new Version(30, 16, 48, 14, 22,
					              new ECBlocks(28, new ECB(1, 49)))));
  return (int)VERSIONS.size();
}
}
}

// file: zxing/datamatrix/decoder/BitMatrixParser.cpp

/*
 *  BitMatrixParser.cpp
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

// #include <zxing/datamatrix/decoder/BitMatrixParser.h>
// #include <zxing/common/IllegalArgumentException.h>

// #include <iostream>

namespace zxing {
namespace datamatrix {

int BitMatrixParser::copyBit(size_t x, size_t y, int versionBits) {
  return bitMatrix_->get(x, y) ? (versionBits << 1) | 0x1 : versionBits << 1;
}

BitMatrixParser::BitMatrixParser(Ref<BitMatrix> bitMatrix) : bitMatrix_(NULL),
                                                             parsedVersion_(NULL),
                                                             readBitMatrix_(NULL) {
  size_t dimension = bitMatrix->getHeight();
  if (dimension < 8 || dimension > 144 || (dimension & 0x01) != 0)
    throw ReaderException("Dimension must be even, > 8 < 144");

  parsedVersion_ = readVersion(bitMatrix);
  bitMatrix_ = extractDataRegion(bitMatrix);
  readBitMatrix_ = new BitMatrix(bitMatrix_->getWidth(), bitMatrix_->getHeight());
}

Ref<Version> BitMatrixParser::readVersion(Ref<BitMatrix> bitMatrix) {
  if (parsedVersion_ != 0) {
    return parsedVersion_;
  }

  int numRows = bitMatrix->getHeight();
  int numColumns = bitMatrix->getWidth();

  Ref<Version> version = parsedVersion_->getVersionForDimensions(numRows, numColumns);
  if (version != 0) {
    return version;
  }
  throw ReaderException("Couldn't decode version");
}

ArrayRef<char> BitMatrixParser::readCodewords() {
    ArrayRef<char> result(parsedVersion_->getTotalCodewords());
    int resultOffset = 0;
    int row = 4;
    int column = 0;

    int numRows = bitMatrix_->getHeight();
    int numColumns = bitMatrix_->getWidth();

    bool corner1Read = false;
    bool corner2Read = false;
    bool corner3Read = false;
    bool corner4Read = false;

    // Read all of the codewords
    do {
      // Check the four corner cases
      if ((row == numRows) && (column == 0) && !corner1Read) {
        result[resultOffset++] = (char) readCorner1(numRows, numColumns);
        row -= 2;
        column +=2;
        corner1Read = true;
      } else if ((row == numRows-2) && (column == 0) && ((numColumns & 0x03) != 0) && !corner2Read) {
        result[resultOffset++] = (char) readCorner2(numRows, numColumns);
        row -= 2;
        column +=2;
        corner2Read = true;
      } else if ((row == numRows+4) && (column == 2) && ((numColumns & 0x07) == 0) && !corner3Read) {
        result[resultOffset++] = (char) readCorner3(numRows, numColumns);
        row -= 2;
        column +=2;
        corner3Read = true;
      } else if ((row == numRows-2) && (column == 0) && ((numColumns & 0x07) == 4) && !corner4Read) {
        result[resultOffset++] = (char) readCorner4(numRows, numColumns);
        row -= 2;
        column +=2;
        corner4Read = true;
      } else {
        // Sweep upward diagonally to the right
        do {
          if ((row < numRows) && (column >= 0) && !readBitMatrix_->get(column, row)) {
            result[resultOffset++] = (char) readUtah(row, column, numRows, numColumns);
          }
          row -= 2;
          column +=2;
        } while ((row >= 0) && (column < numColumns));
        row += 1;
        column +=3;

        // Sweep downward diagonally to the left
        do {
          if ((row >= 0) && (column < numColumns) && !readBitMatrix_->get(column, row)) {
             result[resultOffset++] = (char) readUtah(row, column, numRows, numColumns);
          }
          row += 2;
          column -=2;
        } while ((row < numRows) && (column >= 0));
        row += 3;
        column +=1;
      }
    } while ((row < numRows) || (column < numColumns));

    if (resultOffset != parsedVersion_->getTotalCodewords()) {
      throw ReaderException("Did not read all codewords");
    }
    return result;
}

bool BitMatrixParser::readModule(int row, int column, int numRows, int numColumns) {
    // Adjust the row and column indices based on boundary wrapping
    if (row < 0) {
      row += numRows;
      column += 4 - ((numRows + 4) & 0x07);
    }
    if (column < 0) {
      column += numColumns;
      row += 4 - ((numColumns + 4) & 0x07);
    }
    readBitMatrix_->set(column, row);
    return bitMatrix_->get(column, row);
  }

int BitMatrixParser::readUtah(int row, int column, int numRows, int numColumns) {
    int currentByte = 0;
    if (readModule(row - 2, column - 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(row - 2, column - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(row - 1, column - 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(row - 1, column - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(row - 1, column, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(row, column - 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(row, column - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(row, column, numRows, numColumns)) {
      currentByte |= 1;
    }
    return currentByte;
  }

int BitMatrixParser::readCorner1(int numRows, int numColumns) {
    int currentByte = 0;
    if (readModule(numRows - 1, 0, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(numRows - 1, 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(numRows - 1, 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(1, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(2, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(3, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    return currentByte;
  }

int BitMatrixParser::readCorner2(int numRows, int numColumns) {
    int currentByte = 0;
    if (readModule(numRows - 3, 0, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(numRows - 2, 0, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(numRows - 1, 0, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 4, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 3, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(1, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    return currentByte;
  }

int BitMatrixParser::readCorner3(int numRows, int numColumns) {
    int currentByte = 0;
    if (readModule(numRows - 1, 0, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(numRows - 1, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 3, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(1, numColumns - 3, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(1, numColumns - 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(1, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    return currentByte;
  }

int BitMatrixParser::readCorner4(int numRows, int numColumns) {
    int currentByte = 0;
    if (readModule(numRows - 3, 0, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(numRows - 2, 0, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(numRows - 1, 0, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 2, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(0, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(1, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(2, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    currentByte <<= 1;
    if (readModule(3, numColumns - 1, numRows, numColumns)) {
      currentByte |= 1;
    }
    return currentByte;
  }

Ref<BitMatrix> BitMatrixParser::extractDataRegion(Ref<BitMatrix> bitMatrix) {
    int symbolSizeRows = parsedVersion_->getSymbolSizeRows();
    int symbolSizeColumns = parsedVersion_->getSymbolSizeColumns();

    if ((int)bitMatrix->getHeight() != symbolSizeRows) {
      throw IllegalArgumentException("Dimension of bitMatrix must match the version size");
    }

    int dataRegionSizeRows = parsedVersion_->getDataRegionSizeRows();
    int dataRegionSizeColumns = parsedVersion_->getDataRegionSizeColumns();

    int numDataRegionsRow = symbolSizeRows / dataRegionSizeRows;
    int numDataRegionsColumn = symbolSizeColumns / dataRegionSizeColumns;

    int sizeDataRegionRow = numDataRegionsRow * dataRegionSizeRows;
    int sizeDataRegionColumn = numDataRegionsColumn * dataRegionSizeColumns;

    Ref<BitMatrix> bitMatrixWithoutAlignment(new BitMatrix(sizeDataRegionColumn, sizeDataRegionRow));
    for (int dataRegionRow = 0; dataRegionRow < numDataRegionsRow; ++dataRegionRow) {
      int dataRegionRowOffset = dataRegionRow * dataRegionSizeRows;
      for (int dataRegionColumn = 0; dataRegionColumn < numDataRegionsColumn; ++dataRegionColumn) {
        int dataRegionColumnOffset = dataRegionColumn * dataRegionSizeColumns;
        for (int i = 0; i < dataRegionSizeRows; ++i) {
          int readRowOffset = dataRegionRow * (dataRegionSizeRows + 2) + 1 + i;
          int writeRowOffset = dataRegionRowOffset + i;
          for (int j = 0; j < dataRegionSizeColumns; ++j) {
            int readColumnOffset = dataRegionColumn * (dataRegionSizeColumns + 2) + 1 + j;
            if (bitMatrix->get(readColumnOffset, readRowOffset)) {
              int writeColumnOffset = dataRegionColumnOffset + j;
              bitMatrixWithoutAlignment->set(writeColumnOffset, writeRowOffset);
            }
          }
        }
      }
    }
    return bitMatrixWithoutAlignment;
}

}
}

// file: zxing/datamatrix/decoder/DataBlock.cpp

/*
 *  DataBlock.cpp
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

// #include <zxing/datamatrix/decoder/DataBlock.h>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
namespace datamatrix {

using namespace std;

DataBlock::DataBlock(int numDataCodewords, ArrayRef<char> codewords) :
    numDataCodewords_(numDataCodewords), codewords_(codewords) {
}

int DataBlock::getNumDataCodewords() {
  return numDataCodewords_;
}

ArrayRef<char> DataBlock::getCodewords() {
  return codewords_;
}

std::vector<Ref<DataBlock> > DataBlock::getDataBlocks(ArrayRef<char> rawCodewords, Version *version) {
  // Figure out the number and size of data blocks used by this version and
  // error correction level
  ECBlocks* ecBlocks = version->getECBlocks();

  // First count the total number of data blocks
  int totalBlocks = 0;
  vector<ECB*> ecBlockArray = ecBlocks->getECBlocks();
  for (size_t i = 0; i < ecBlockArray.size(); i++) {
    totalBlocks += ecBlockArray[i]->getCount();
  }

  // Now establish DataBlocks of the appropriate size and number of data codewords
  std::vector<Ref<DataBlock> > result(totalBlocks);
  int numResultBlocks = 0;
  for (size_t j = 0; j < ecBlockArray.size(); j++) {
    ECB *ecBlock = ecBlockArray[j];
    for (int i = 0; i < ecBlock->getCount(); i++) {
      int numDataCodewords = ecBlock->getDataCodewords();
      int numBlockCodewords = ecBlocks->getECCodewords() + numDataCodewords;
      ArrayRef<char> buffer(numBlockCodewords);
      Ref<DataBlock> blockRef(new DataBlock(numDataCodewords, buffer));
      result[numResultBlocks++] = blockRef;
    }
  }

  // All blocks have the same amount of data, except that the last n
  // (where n may be 0) have 1 more byte. Figure out where these start.
  int shorterBlocksTotalCodewords = (int)result[0]->codewords_->size();
  int longerBlocksStartAt = (int)result.size() - 1;
  while (longerBlocksStartAt >= 0) {
    int numCodewords = (int)result[longerBlocksStartAt]->codewords_->size();
    if (numCodewords == shorterBlocksTotalCodewords) {
      break;
    }
    if (numCodewords != shorterBlocksTotalCodewords + 1) {
      throw IllegalArgumentException("Data block sizes differ by more than 1");
    }
    longerBlocksStartAt--;
  }
  longerBlocksStartAt++;

  int shorterBlocksNumDataCodewords = shorterBlocksTotalCodewords - ecBlocks->getECCodewords();
  // The last elements of result may be 1 element longer;
  // first fill out as many elements as all of them have
  int rawCodewordsOffset = 0;
  for (int i = 0; i < shorterBlocksNumDataCodewords; i++) {
    for (int j = 0; j < numResultBlocks; j++) {
      result[j]->codewords_[i] = rawCodewords[rawCodewordsOffset++];
    }
  }
  // Fill out the last data block in the longer ones
  for (int j = longerBlocksStartAt; j < numResultBlocks; j++) {
    result[j]->codewords_[shorterBlocksNumDataCodewords] = rawCodewords[rawCodewordsOffset++];
  }
  // Now add in error correction blocks
  int max = (int)result[0]->codewords_->size();
  for (int i = shorterBlocksNumDataCodewords; i < max; i++) {
    for (int j = 0; j < numResultBlocks; j++) {
      int iOffset = j < longerBlocksStartAt ? i : i + 1;
      result[j]->codewords_[iOffset] = rawCodewords[rawCodewordsOffset++];
    }
  }

  if (rawCodewordsOffset != rawCodewords->size()) {
    throw IllegalArgumentException("rawCodewordsOffset != rawCodewords.length");
  }

  return result;
}

}
}

// file: zxing/datamatrix/decoder/DecodedBitStreamParser.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  DecodedBitStreamParser.cpp
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

// #include <zxing/FormatException.h>
// #include <zxing/datamatrix/decoder/DecodedBitStreamParser.h>
// #include <iostream>
// #include <zxing/common/DecoderResult.h>

namespace zxing {
namespace datamatrix {

using namespace std;

const char DecodedBitStreamParser::C40_BASIC_SET_CHARS[] = {
    '*', '*', '*', ' ', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N',
    'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'
};

const char DecodedBitStreamParser::C40_SHIFT2_SET_CHARS[] = {
    '!', '"', '#', '$', '%', '&', '\'', '(', ')', '*', '+', ',', '-', '.',
    '/', ':', ';', '<', '=', '>', '?', '@', '[', '\\', ']', '^', '_'
};

const char DecodedBitStreamParser::TEXT_BASIC_SET_CHARS[] = {
    '*', '*', '*', ' ', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n',
    'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'
};

const char DecodedBitStreamParser::TEXT_SHIFT3_SET_CHARS[] = {
    '\'', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N',
    'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z', '{', '|', '}', '~', (char) 127
};

Ref<DecoderResult> DecodedBitStreamParser::decode(ArrayRef<char> bytes) {
  Ref<BitSource> bits(new BitSource(bytes));
  ostringstream result;
  ostringstream resultTrailer;
  vector<char> byteSegments;
  int mode = ASCII_ENCODE;
  do {
    if (mode == ASCII_ENCODE) {
      mode = decodeAsciiSegment(bits, result, resultTrailer);
    } else {
      switch (mode) {
        case C40_ENCODE:
          decodeC40Segment(bits, result);
          break;
        case TEXT_ENCODE:
          decodeTextSegment(bits, result);
          break;
        case ANSIX12_ENCODE:
          decodeAnsiX12Segment(bits, result);
          break;
        case EDIFACT_ENCODE:
          decodeEdifactSegment(bits, result);
          break;
        case BASE256_ENCODE:
          decodeBase256Segment(bits, result, byteSegments);
          break;
        default:
          throw FormatException("Unsupported mode indicator");
      }
      mode = ASCII_ENCODE;
    }
  } while (mode != PAD_ENCODE && bits->available() > 0);

  if (resultTrailer.str().size() > 0) {
    result << resultTrailer.str();
  }
  ArrayRef<char> rawBytes(bytes);
  Ref<String> text(new String(result.str()));
  return Ref<DecoderResult>(new DecoderResult(rawBytes, text));
}

int DecodedBitStreamParser::decodeAsciiSegment(Ref<BitSource> bits, ostringstream & result,
  ostringstream & resultTrailer) {
  bool upperShift = false;
  do {
    int oneByte = bits->readBits(8);
    if (oneByte == 0) {
      throw FormatException("Not enough bits to decode");
    } else if (oneByte <= 128) {  // ASCII data (ASCII value + 1)
      oneByte = upperShift ? (oneByte + 128) : oneByte;
      // upperShift = false;
      result << (char) (oneByte - 1);
      return ASCII_ENCODE;
    } else if (oneByte == 129) {  // Pad
      return PAD_ENCODE;
    } else if (oneByte <= 229) {  // 2-digit data 00-99 (Numeric Value + 130)
      int value = oneByte - 130;
      if (value < 10) { // padd with '0' for single digit values
        result << '0';
      }
      result << value;
    } else if (oneByte == 230) {  // Latch to C40 encodation
      return C40_ENCODE;
    } else if (oneByte == 231) {  // Latch to Base 256 encodation
      return BASE256_ENCODE;
    } else if (oneByte == 232) {  // FNC1
      result << ((char) 29); // translate as ASCII 29
    } else if (oneByte == 233 || oneByte == 234) {
      // Structured Append, Reader Programming
      // Ignore these symbols for now
      // throw FormatException.getInstance();
    } else if (oneByte == 235) {  // Upper Shift (shift to Extended ASCII)
      upperShift = true;
    } else if (oneByte == 236) {  // 05 Macro
        result << ("[)>RS05GS");
        resultTrailer << ("RSEOT");
    } else if (oneByte == 237) {  // 06 Macro
      result << ("[)>RS06GS");
      resultTrailer <<  ("RSEOT");
    } else if (oneByte == 238) {  // Latch to ANSI X12 encodation
      return ANSIX12_ENCODE;
    } else if (oneByte == 239) {  // Latch to Text encodation
      return TEXT_ENCODE;
    } else if (oneByte == 240) {  // Latch to EDIFACT encodation
      return EDIFACT_ENCODE;
    } else if (oneByte == 241) {  // ECI Character
      // TODO(bbrown): I think we need to support ECI
      // throw FormatException.getInstance();
      // Ignore this symbol for now
    } else if (oneByte >= 242) { // Not to be used in ASCII encodation
      // ... but work around encoders that end with 254, latch back to ASCII
      if (oneByte != 254 || bits->available() != 0) {
        throw FormatException("Not to be used in ASCII encodation");
      }
    }
  } while (bits->available() > 0);
  return ASCII_ENCODE;
}

void DecodedBitStreamParser::decodeC40Segment(Ref<BitSource> bits, ostringstream & result) {
  // Three C40 values are encoded in a 16-bit value as
  // (1600 * C1) + (40 * C2) + C3 + 1
  // TODO(bbrown): The Upper Shift with C40 doesn't work in the 4 value scenario all the time
  bool upperShift = false;

  int cValues[3];
  int shift = 0;
  do {
    // If there is only one byte left then it will be encoded as ASCII
    if (bits->available() == 8) {
      return;
    }
    int firstByte = bits->readBits(8);
    if (firstByte == 254) {  // Unlatch codeword
      return;
    }

    parseTwoBytes(firstByte, bits->readBits(8), cValues);

    for (int i = 0; i < 3; i++) {
      int cValue = cValues[i];
      switch (shift) {
        case 0:
          if (cValue < 3) {
            shift = cValue + 1;
          } else {
            if (upperShift) {
              result << (char) (C40_BASIC_SET_CHARS[cValue] + 128);
              upperShift = false;
            } else {
              result << C40_BASIC_SET_CHARS[cValue];
            }
          }
          break;
        case 1:
          if (upperShift) {
            result << (char) (cValue + 128);
            upperShift = false;
          } else {
            result << (char) cValue;
          }
          shift = 0;
          break;
        case 2:
          if (cValue < 27) {
            if (upperShift) {
              result << (char) (C40_SHIFT2_SET_CHARS[cValue] + 128);
              upperShift = false;
            } else {
              result << C40_SHIFT2_SET_CHARS[cValue];
            }
          } else if (cValue == 27) {  // FNC1
            result << ((char) 29); // translate as ASCII 29
          } else if (cValue == 30) {  // Upper Shift
            upperShift = true;
          } else {
            throw FormatException("decodeC40Segment: Upper Shift");
          }
          shift = 0;
          break;
        case 3:
          if (upperShift) {
            result << (char) (cValue + 224);
            upperShift = false;
          } else {
            result << (char) (cValue + 96);
          }
          shift = 0;
          break;
        default:
          throw FormatException("decodeC40Segment: no case");
      }
    }
  } while (bits->available() > 0);
}

void DecodedBitStreamParser::decodeTextSegment(Ref<BitSource> bits, ostringstream & result) {
  // Three Text values are encoded in a 16-bit value as
  // (1600 * C1) + (40 * C2) + C3 + 1
  // TODO(bbrown): The Upper Shift with Text doesn't work in the 4 value scenario all the time
  bool upperShift = false;

  int cValues[3];
  int shift = 0;
  do {
    // If there is only one byte left then it will be encoded as ASCII
    if (bits->available() == 8) {
      return;
    }
    int firstByte = bits->readBits(8);
    if (firstByte == 254) {  // Unlatch codeword
      return;
    }

    parseTwoBytes(firstByte, bits->readBits(8), cValues);

    for (int i = 0; i < 3; i++) {
      int cValue = cValues[i];
      switch (shift) {
        case 0:
          if (cValue < 3) {
            shift = cValue + 1;
          } else {
            if (upperShift) {
              result << (char) (TEXT_BASIC_SET_CHARS[cValue] + 128);
              upperShift = false;
            } else {
              result << (TEXT_BASIC_SET_CHARS[cValue]);
            }
          }
          break;
        case 1:
          if (upperShift) {
            result << (char) (cValue + 128);
            upperShift = false;
          } else {
            result << (char) (cValue);
          }
          shift = 0;
          break;
        case 2:
          // Shift 2 for Text is the same encoding as C40
          if (cValue < 27) {
            if (upperShift) {
              result << (char) (C40_SHIFT2_SET_CHARS[cValue] + 128);
              upperShift = false;
            } else {
              result << (C40_SHIFT2_SET_CHARS[cValue]);
            }
          } else if (cValue == 27) {  // FNC1
            result << ((char) 29); // translate as ASCII 29
          } else if (cValue == 30) {  // Upper Shift
            upperShift = true;
          } else {
            throw FormatException("decodeTextSegment: Upper Shift");
          }
          shift = 0;
          break;
        case 3:
          if (upperShift) {
            result << (char) (TEXT_SHIFT3_SET_CHARS[cValue] + 128);
            upperShift = false;
          } else {
            result << (TEXT_SHIFT3_SET_CHARS[cValue]);
          }
          shift = 0;
          break;
        default:
          throw FormatException("decodeTextSegment: no case");
      }
    }
  } while (bits->available() > 0);
}

void DecodedBitStreamParser::decodeAnsiX12Segment(Ref<BitSource> bits, ostringstream & result) {
  // Three ANSI X12 values are encoded in a 16-bit value as
  // (1600 * C1) + (40 * C2) + C3 + 1

  int cValues[3];
  do {
    // If there is only one byte left then it will be encoded as ASCII
    if (bits->available() == 8) {
      return;
    }
    int firstByte = bits->readBits(8);
    if (firstByte == 254) {  // Unlatch codeword
      return;
    }

    parseTwoBytes(firstByte, bits->readBits(8), cValues);

    for (int i = 0; i < 3; i++) {
      int cValue = cValues[i];
      if (cValue == 0) {  // X12 segment terminator <CR>
        result << '\r';
      } else if (cValue == 1) {  // X12 segment separator *
        result << '*';
      } else if (cValue == 2) {  // X12 sub-element separator >
        result << '>';
      } else if (cValue == 3) {  // space
        result << ' ';
      } else if (cValue < 14) {  // 0 - 9
        result << (char) (cValue + 44);
      } else if (cValue < 40) {  // A - Z
        result << (char) (cValue + 51);
      } else {
        throw FormatException("decodeAnsiX12Segment: no case");
      }
    }
  } while (bits->available() > 0);
}

void DecodedBitStreamParser::parseTwoBytes(int firstByte, int secondByte, int* result) {
  int fullBitValue = (firstByte << 8) + secondByte - 1;
  int temp = fullBitValue / 1600;
  result[0] = temp;
  fullBitValue -= temp * 1600;
  temp = fullBitValue / 40;
  result[1] = temp;
  result[2] = fullBitValue - temp * 40;
}

void DecodedBitStreamParser::decodeEdifactSegment(Ref<BitSource> bits, ostringstream & result) {
  do {
    // If there is only two or less bytes left then it will be encoded as ASCII
    if (bits->available() <= 16) {
      return;
    }

    for (int i = 0; i < 4; i++) {
      int edifactValue = bits->readBits(6);

      // Check for the unlatch character
      if (edifactValue == 0x1f) {  // 011111
        // Read rest of byte, which should be 0, and stop
        int bitsLeft = 8 - bits->getBitOffset();
        if (bitsLeft != 8) {
          bits->readBits(bitsLeft);
        }
        return;
      }

      if ((edifactValue & 0x20) == 0) {  // no 1 in the leading (6th) bit
        edifactValue |= 0x40;  // Add a leading 01 to the 6 bit binary value
      }
      result << (char)(edifactValue);
    }
  } while (bits->available() > 0);
}

void DecodedBitStreamParser::decodeBase256Segment(Ref<BitSource> bits, ostringstream& result, vector<char> byteSegments) {
  // Figure out how long the Base 256 Segment is.
  int codewordPosition = 1 + bits->getByteOffset(); // position is 1-indexed
  int d1 = unrandomize255State(bits->readBits(8), codewordPosition++);
  int count;
  if (d1 == 0) {  // Read the remainder of the symbol
    count = bits->available() / 8;
  } else if (d1 < 250) {
    count = d1;
  } else {
    count = 250 * (d1 - 249) + unrandomize255State(bits->readBits(8), codewordPosition++);
  }

  // We're seeing NegativeArraySizeException errors from users.
  if (count < 0) {
    throw FormatException("NegativeArraySizeException");
  }

  for (int i = 0; i < count; i++) {
    // Have seen this particular error in the wild, such as at
    // http://www.bcgen.com/demo/IDAutomationStreamingDataMatrix.aspx?MODE=3&D=Fred&PFMT=3&PT=F&X=0.3&O=0&LM=0.2
    if (bits->available() < 8) {
      throw FormatException("byteSegments");
    }
    char byte = unrandomize255State(bits->readBits(8), codewordPosition++);
    byteSegments.push_back(byte);
    result << byte;
  }
}
}
}

// file: zxing/datamatrix/decoder/Decoder.cpp

/*
 *  Decoder.cpp
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

// #include <zxing/datamatrix/decoder/Decoder.h>
// #include <zxing/datamatrix/decoder/BitMatrixParser.h>
// #include <zxing/datamatrix/decoder/DataBlock.h>
// #include <zxing/datamatrix/decoder/DecodedBitStreamParser.h>
// #include <zxing/datamatrix/Version.h>
// #include <zxing/ReaderException.h>
// #include <zxing/ChecksumException.h>
// #include <zxing/common/reedsolomon/ReedSolomonException.h>

namespace zxing {
namespace datamatrix {
        
using namespace std;
        
Decoder::Decoder() : rsDecoder_(GenericGF::DATA_MATRIX_FIELD_256) {}

void Decoder::correctErrors(ArrayRef<char> codewordBytes, int numDataCodewords) {
  int numCodewords = (int)codewordBytes->size();
  ArrayRef<int> codewordInts(numCodewords);
  for (int i = 0; i < numCodewords; i++) {
    codewordInts[i] = codewordBytes[i] & 0xff;
  }
  int numECCodewords = numCodewords - numDataCodewords;
  try {
    rsDecoder_.decode(codewordInts, numECCodewords);
  } catch (ReedSolomonException const& ignored) {
    (void)ignored;
    throw ChecksumException();
  }
  // Copy back into array of bytes -- only need to worry about the bytes that were data
  // We don't care about errors in the error-correction codewords
  for (int i = 0; i < numDataCodewords; i++) {
    codewordBytes[i] = (char)codewordInts[i];
  }
}

Ref<DecoderResult> Decoder::decode(Ref<BitMatrix> bits) {
  // Construct a parser and read version, error-correction level
  BitMatrixParser parser(bits);
  Version *version = parser.readVersion(bits);

  // Read codewords
  ArrayRef<char> codewords(parser.readCodewords());
  // Separate into data blocks
  std::vector<Ref<DataBlock> > dataBlocks = DataBlock::getDataBlocks(codewords, version);

  int dataBlocksCount = (int)dataBlocks.size();

  // Count total number of data bytes
  int totalBytes = 0;
  for (int i = 0; i < dataBlocksCount; i++) {
    totalBytes += dataBlocks[i]->getNumDataCodewords();
  }
  ArrayRef<char> resultBytes(totalBytes);

  // Error-correct and copy data blocks together into a stream of bytes
  for (int j = 0; j < dataBlocksCount; j++) {
    Ref<DataBlock> dataBlock(dataBlocks[j]);
    ArrayRef<char> codewordBytes = dataBlock->getCodewords();
    int numDataCodewords = dataBlock->getNumDataCodewords();
    correctErrors(codewordBytes, numDataCodewords);
    for (int i = 0; i < numDataCodewords; i++) {
      // De-interlace data blocks.
      resultBytes[i * dataBlocksCount + j] = codewordBytes[i];
    }
  }
  // Decode the contents of that stream of bytes
  DecodedBitStreamParser decodedBSParser;
  return Ref<DecoderResult> (decodedBSParser.decode(resultBytes));
}
}
}

// file: zxing/datamatrix/detector/CornerPoint.cpp

/*
 *  CornerPoint.cpp
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

// #include <zxing/datamatrix/detector/CornerPoint.h>


namespace zxing {
	namespace datamatrix {

		using namespace std;

		CornerPoint::CornerPoint(float posX, float posY) :
		  ResultPoint(posX,posY), counter_(0) {
		}

		int CornerPoint::getCount() const {
			return counter_;
		}

		void CornerPoint::incrementCount() {
			counter_++;
		}

		bool CornerPoint::equals(Ref<CornerPoint> other) const {
			return posX_ == other->getX() && posY_ == other->getY();
		}

	}
}

// file: zxing/datamatrix/detector/Detector.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Detector.cpp
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

// #include <map>
// #include <zxing/ResultPoint.h>
// #include <zxing/common/GridSampler.h>
// #include <zxing/datamatrix/detector/Detector.h>
// #include <zxing/common/detector/MathUtils.h>
// #include <zxing/NotFoundException.h>
// #include <sstream>
// #include <cstdlib>
// #include <algorithm>  // vs12, std::min und std:max

namespace zxing {
    namespace datamatrix {
        namespace {
            typedef std::map<Ref<ResultPoint>, int> PointMap;
            void increment(PointMap& table, Ref<ResultPoint> const& key) {
                int& value = table[key];
                value += 1;
            }
        }
       
        using namespace std;
        
ResultPointsAndTransitions::ResultPointsAndTransitions() {
  Ref<ResultPoint> ref(new ResultPoint(0, 0));
  from_ = ref;
  to_ = ref;
  transitions_ = 0;
}

ResultPointsAndTransitions::ResultPointsAndTransitions(Ref<ResultPoint> from, Ref<ResultPoint> to,
                                                       int transitions)
  : to_(to), from_(from), transitions_(transitions) {
}

Ref<ResultPoint> ResultPointsAndTransitions::getFrom() {
  return from_;
}

Ref<ResultPoint> ResultPointsAndTransitions::getTo() {
  return to_;
}

int ResultPointsAndTransitions::getTransitions() {
  return transitions_;
}

Detector::Detector(Ref<BitMatrix> image)
  : image_(image) {
}

Ref<BitMatrix> Detector::getImage() {
  return image_;
}

Ref<DetectorResult> Detector::detect() {
  Ref<WhiteRectangleDetector> rectangleDetector_(new WhiteRectangleDetector(image_));
  std::vector<Ref<ResultPoint> > ResultPoints = rectangleDetector_->detect();
  Ref<ResultPoint> pointA = ResultPoints[0];
  Ref<ResultPoint> pointB = ResultPoints[1];
  Ref<ResultPoint> pointC = ResultPoints[2];
  Ref<ResultPoint> pointD = ResultPoints[3];

  // Point A and D are across the diagonal from one another,
  // as are B and C. Figure out which are the solid black lines
  // by counting transitions
  std::vector<Ref<ResultPointsAndTransitions> > transitions(4);
  transitions[0].reset(transitionsBetween(pointA, pointB));
  transitions[1].reset(transitionsBetween(pointA, pointC));
  transitions[2].reset(transitionsBetween(pointB, pointD));
  transitions[3].reset(transitionsBetween(pointC, pointD));
  insertionSort(transitions);

  // Sort by number of transitions. First two will be the two solid sides; last two
  // will be the two alternating black/white sides
  Ref<ResultPointsAndTransitions> lSideOne(transitions[0]);
  Ref<ResultPointsAndTransitions> lSideTwo(transitions[1]);

  // Figure out which point is their intersection by tallying up the number of times we see the
  // endpoints in the four endpoints. One will show up twice.
  typedef std::map<Ref<ResultPoint>, int> PointMap;
  PointMap pointCount;
  increment(pointCount, lSideOne->getFrom());
  increment(pointCount, lSideOne->getTo());
  increment(pointCount, lSideTwo->getFrom());
  increment(pointCount, lSideTwo->getTo());

  // Figure out which point is their intersection by tallying up the number of times we see the
  // endpoints in the four endpoints. One will show up twice.
  Ref<ResultPoint> maybeTopLeft;
  Ref<ResultPoint> bottomLeft;
  Ref<ResultPoint> maybeBottomRight;
  for (PointMap::const_iterator entry = pointCount.begin(), end = pointCount.end(); entry != end; ++entry) {
    Ref<ResultPoint> const& point = entry->first;
    int value = entry->second;
    if (value == 2) {
      bottomLeft = point; // this is definitely the bottom left, then -- end of two L sides
    } else {
      // Otherwise it's either top left or bottom right -- just assign the two arbitrarily now
      if (maybeTopLeft == 0) {
        maybeTopLeft = point;
      } else {
        maybeBottomRight = point;
      }
    }
  }

  if (maybeTopLeft == 0 || bottomLeft == 0 || maybeBottomRight == 0) {
    throw NotFoundException();
  }

  // Bottom left is correct but top left and bottom right might be switched
  std::vector<Ref<ResultPoint> > corners(3);
  corners[0].reset(maybeTopLeft);
  corners[1].reset(bottomLeft);
  corners[2].reset(maybeBottomRight);

  // Use the dot product trick to sort them out
  ResultPoint::orderBestPatterns(corners);

  // Now we know which is which:
  Ref<ResultPoint> bottomRight(corners[0]);
  bottomLeft = corners[1];
  Ref<ResultPoint> topLeft(corners[2]);

  // Which point didn't we find in relation to the "L" sides? that's the top right corner
  Ref<ResultPoint> topRight;
  if (!(pointA->equals(bottomRight) || pointA->equals(bottomLeft) || pointA->equals(topLeft))) {
    topRight = pointA;
  } else if (!(pointB->equals(bottomRight) || pointB->equals(bottomLeft)
               || pointB->equals(topLeft))) {
    topRight = pointB;
  } else if (!(pointC->equals(bottomRight) || pointC->equals(bottomLeft)
               || pointC->equals(topLeft))) {
    topRight = pointC;
  } else {
    topRight = pointD;
  }

  // Next determine the dimension by tracing along the top or right side and counting black/white
  // transitions. Since we start inside a black module, we should see a number of transitions
  // equal to 1 less than the code dimension. Well, actually 2 less, because we are going to
  // end on a black module:

  // The top right point is actually the corner of a module, which is one of the two black modules
  // adjacent to the white module at the top right. Tracing to that corner from either the top left
  // or bottom right should work here.

  int dimensionTop = transitionsBetween(topLeft, topRight)->getTransitions();
  int dimensionRight = transitionsBetween(bottomRight, topRight)->getTransitions();

  //dimensionTop++;
  if ((dimensionTop & 0x01) == 1) {
    // it can't be odd, so, round... up?
    dimensionTop++;
  }
  dimensionTop += 2;

  //dimensionRight++;
  if ((dimensionRight & 0x01) == 1) {
    // it can't be odd, so, round... up?
    dimensionRight++;
  }
  dimensionRight += 2;

  Ref<BitMatrix> bits;
  Ref<PerspectiveTransform> transform;
  Ref<ResultPoint> correctedTopRight;


  // Rectanguar symbols are 6x16, 6x28, 10x24, 10x32, 14x32, or 14x44. If one dimension is more
  // than twice the other, it's certainly rectangular, but to cut a bit more slack we accept it as
  // rectangular if the bigger side is at least 7/4 times the other:
  if (4 * dimensionTop >= 7 * dimensionRight || 4 * dimensionRight >= 7 * dimensionTop) {
    // The matrix is rectangular
    correctedTopRight = correctTopRightRectangular(bottomLeft, bottomRight, topLeft, topRight,
                                                   dimensionTop, dimensionRight);
    if (correctedTopRight == NULL) {
      correctedTopRight = topRight;
    }

    dimensionTop = transitionsBetween(topLeft, correctedTopRight)->getTransitions();
    dimensionRight = transitionsBetween(bottomRight, correctedTopRight)->getTransitions();

    if ((dimensionTop & 0x01) == 1) {
      // it can't be odd, so, round... up?
      dimensionTop++;
    }

    if ((dimensionRight & 0x01) == 1) {
      // it can't be odd, so, round... up?
      dimensionRight++;
    }

    transform = createTransform(topLeft, correctedTopRight, bottomLeft, bottomRight, dimensionTop,
                                dimensionRight);
    bits = sampleGrid(image_, dimensionTop, dimensionRight, transform);

  } else {
    // The matrix is square
    int dimension = min(dimensionRight, dimensionTop);

    // correct top right point to match the white module
    correctedTopRight = correctTopRight(bottomLeft, bottomRight, topLeft, topRight, dimension);
    if (correctedTopRight == NULL) {
      correctedTopRight = topRight;
    }

    // Redetermine the dimension using the corrected top right point
    int dimensionCorrected = std::max(transitionsBetween(topLeft, correctedTopRight)->getTransitions(),
                                      transitionsBetween(bottomRight, correctedTopRight)->getTransitions());
    dimensionCorrected++;
    if ((dimensionCorrected & 0x01) == 1) {
      dimensionCorrected++;
    }

    transform = createTransform(topLeft, correctedTopRight, bottomLeft, bottomRight,
                                dimensionCorrected, dimensionCorrected);
    bits = sampleGrid(image_, dimensionCorrected, dimensionCorrected, transform);
  }

  ArrayRef< Ref<ResultPoint> > points (new Array< Ref<ResultPoint> >(4));
  points[0].reset(topLeft);
  points[1].reset(bottomLeft);
  points[2].reset(correctedTopRight);
  points[3].reset(bottomRight);
  Ref<DetectorResult> detectorResult(new DetectorResult(bits, points));
  return detectorResult;
}

/**
 * Calculates the position of the white top right module using the output of the rectangle detector
 * for a rectangular matrix
 */
Ref<ResultPoint> Detector::correctTopRightRectangular(Ref<ResultPoint> bottomLeft,
                                                      Ref<ResultPoint> bottomRight, Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight,
                                                      int dimensionTop, int dimensionRight) {

  float corr = distance(bottomLeft, bottomRight) / (float) dimensionTop;
  int norm = distance(topLeft, topRight);
  float cos = (topRight->getX() - topLeft->getX()) / norm;
  float sin = (topRight->getY() - topLeft->getY()) / norm;

  Ref<ResultPoint> c1(
    new ResultPoint(topRight->getX() + corr * cos, topRight->getY() + corr * sin));

  corr = distance(bottomLeft, topLeft) / (float) dimensionRight;
  norm = distance(bottomRight, topRight);
  cos = (topRight->getX() - bottomRight->getX()) / norm;
  sin = (topRight->getY() - bottomRight->getY()) / norm;

  Ref<ResultPoint> c2(
    new ResultPoint(topRight->getX() + corr * cos, topRight->getY() + corr * sin));

  if (!isValid(c1)) {
    if (isValid(c2)) {
      return c2;
    }
    return Ref<ResultPoint>(NULL);
  }
  if (!isValid(c2)) {
    return c1;
  }

  int l1 = abs(dimensionTop - transitionsBetween(topLeft, c1)->getTransitions())
    + abs(dimensionRight - transitionsBetween(bottomRight, c1)->getTransitions());
  int l2 = abs(dimensionTop - transitionsBetween(topLeft, c2)->getTransitions())
    + abs(dimensionRight - transitionsBetween(bottomRight, c2)->getTransitions());

  return l1 <= l2 ? c1 : c2;
}

/**
 * Calculates the position of the white top right module using the output of the rectangle detector
 * for a square matrix
 */
Ref<ResultPoint> Detector::correctTopRight(Ref<ResultPoint> bottomLeft,
                                           Ref<ResultPoint> bottomRight, Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight,
                                           int dimension) {

  float corr = distance(bottomLeft, bottomRight) / (float) dimension;
  int norm = distance(topLeft, topRight);
  float cos = (topRight->getX() - topLeft->getX()) / norm;
  float sin = (topRight->getY() - topLeft->getY()) / norm;

  Ref<ResultPoint> c1(
    new ResultPoint(topRight->getX() + corr * cos, topRight->getY() + corr * sin));

  corr = distance(bottomLeft, topLeft) / (float) dimension;
  norm = distance(bottomRight, topRight);
  cos = (topRight->getX() - bottomRight->getX()) / norm;
  sin = (topRight->getY() - bottomRight->getY()) / norm;

  Ref<ResultPoint> c2(
    new ResultPoint(topRight->getX() + corr * cos, topRight->getY() + corr * sin));

  if (!isValid(c1)) {
    if (isValid(c2)) {
      return c2;
    }
    return Ref<ResultPoint>(NULL);
  }
  if (!isValid(c2)) {
    return c1;
  }

  int l1 = abs(
    transitionsBetween(topLeft, c1)->getTransitions()
    - transitionsBetween(bottomRight, c1)->getTransitions());
  int l2 = abs(
    transitionsBetween(topLeft, c2)->getTransitions()
    - transitionsBetween(bottomRight, c2)->getTransitions());

  return l1 <= l2 ? c1 : c2;
}

bool Detector::isValid(Ref<ResultPoint> p) {
  return p->getX() >= 0 && p->getX() < image_->getWidth() && p->getY() > 0
    && p->getY() < image_->getHeight();
}

int Detector::distance(Ref<ResultPoint> a, Ref<ResultPoint> b) {
  return MathUtils::round(ResultPoint::distance(a, b));
}

Ref<ResultPointsAndTransitions> Detector::transitionsBetween(Ref<ResultPoint> from,
                                                             Ref<ResultPoint> to) {
  // See QR Code Detector, sizeOfBlackWhiteBlackRun()
  int fromX = (int) from->getX();
  int fromY = (int) from->getY();
  int toX = (int) to->getX();
  int toY = (int) to->getY();
  bool steep = abs(toY - fromY) > abs(toX - fromX);
  if (steep) {
    int temp = fromX;
    fromX = fromY;
    fromY = temp;
    temp = toX;
    toX = toY;
    toY = temp;
  }

  int dx = abs(toX - fromX);
  int dy = abs(toY - fromY);
  int error = -dx >> 1;
  int ystep = fromY < toY ? 1 : -1;
  int xstep = fromX < toX ? 1 : -1;
  int transitions = 0;
  bool inBlack = image_->get(steep ? fromY : fromX, steep ? fromX : fromY);
  for (int x = fromX, y = fromY; x != toX; x += xstep) {
    bool isBlack = image_->get(steep ? y : x, steep ? x : y);
    if (isBlack != inBlack) {
      transitions++;
      inBlack = isBlack;
    }
    error += dy;
    if (error > 0) {
      if (y == toY) {
        break;
      }
      y += ystep;
      error -= dx;
    }
  }
  Ref<ResultPointsAndTransitions> result(new ResultPointsAndTransitions(from, to, transitions));
  return result;
}

Ref<PerspectiveTransform> Detector::createTransform(Ref<ResultPoint> topLeft,
                                                    Ref<ResultPoint> topRight, Ref<ResultPoint> bottomLeft, Ref<ResultPoint> bottomRight,
                                                    int dimensionX, int dimensionY) {

  Ref<PerspectiveTransform> transform(
    PerspectiveTransform::quadrilateralToQuadrilateral(
      0.5f,
      0.5f,
      dimensionX - 0.5f,
      0.5f,
      dimensionX - 0.5f,
      dimensionY - 0.5f,
      0.5f,
      dimensionY - 0.5f,
      topLeft->getX(),
      topLeft->getY(),
      topRight->getX(),
      topRight->getY(),
      bottomRight->getX(),
      bottomRight->getY(),
      bottomLeft->getX(),
      bottomLeft->getY()));
  return transform;
}

Ref<BitMatrix> Detector::sampleGrid(Ref<BitMatrix> image, int dimensionX, int dimensionY,
                                    Ref<PerspectiveTransform> transform) {
  GridSampler &sampler = GridSampler::getInstance();
  return sampler.sampleGrid(image, dimensionX, dimensionY, transform);
}

void Detector::insertionSort(std::vector<Ref<ResultPointsAndTransitions> > &vector) {
  int max = (int)vector.size();
  bool swapped = true;
  Ref<ResultPointsAndTransitions> value;
  Ref<ResultPointsAndTransitions> valueB;
  do {
    swapped = false;
    for (int i = 1; i < max; i++) {
      value = vector[i - 1];
      if (compare(value, (valueB = vector[i])) > 0){
        swapped = true;
        vector[i - 1].reset(valueB);
        vector[i].reset(value);
      }
    }
  } while (swapped);
}

int Detector::compare(Ref<ResultPointsAndTransitions> a, Ref<ResultPointsAndTransitions> b) {
  return a->getTransitions() - b->getTransitions();
}
}
}

// file: zxing/datamatrix/detector/DetectorException.cpp

/*
 * DetectorException.cpp
 *
 *  Created on: Aug 26, 2011
 *      Author: luiz
 */

// #include "DetectorException.h"

namespace zxing {
namespace datamatrix {

DetectorException::DetectorException(const char *msg) :
    Exception(msg) {

}

DetectorException::~DetectorException() throw () {
  // TODO Auto-generated destructor stub
}

}
} /* namespace zxing */

// file: zxing/multi/ByQuadrantReader.cpp

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

// #include <zxing/multi/ByQuadrantReader.h>
// #include <zxing/ReaderException.h>

namespace zxing {
namespace multi {

ByQuadrantReader::ByQuadrantReader(Reader& delegate) : delegate_(delegate) {}

ByQuadrantReader::~ByQuadrantReader(){}

Ref<Result> ByQuadrantReader::decode(Ref<BinaryBitmap> image){
  return decode(image, DecodeHints::DEFAULT_HINT);
}

Ref<Result> ByQuadrantReader::decode(Ref<BinaryBitmap> image, DecodeHints hints){
  int width = image->getWidth();
  int height = image->getHeight();
  int halfWidth = width / 2;
  int halfHeight = height / 2;
  Ref<BinaryBitmap> topLeft = image->crop(0, 0, halfWidth, halfHeight);
  try {
    return delegate_.decode(topLeft, hints);
  } catch (ReaderException const& re) {
    (void)re;
    // continue
  }

  Ref<BinaryBitmap> topRight = image->crop(halfWidth, 0, halfWidth, halfHeight);
  try {
    return delegate_.decode(topRight, hints);
  } catch (ReaderException const& re) {
    (void)re;
    // continue
  }

  Ref<BinaryBitmap> bottomLeft = image->crop(0, halfHeight, halfWidth, halfHeight);
  try {
    return delegate_.decode(bottomLeft, hints);
  } catch (ReaderException const& re) {
    (void)re;
    // continue
  }

  Ref<BinaryBitmap> bottomRight = image->crop(halfWidth, halfHeight, halfWidth, halfHeight);
  try {
    return delegate_.decode(bottomRight, hints);
  } catch (ReaderException const& re) {
    (void)re;
    // continue
  }

  int quarterWidth = halfWidth / 2;
  int quarterHeight = halfHeight / 2;
  Ref<BinaryBitmap> center = image->crop(quarterWidth, quarterHeight, halfWidth, halfHeight);
  return delegate_.decode(center, hints);
}

} // End zxing::multi namespace
} // End zxing namespace

// file: zxing/multi/GenericMultipleBarcodeReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/multi/GenericMultipleBarcodeReader.h>
// #include <zxing/ReaderException.h>
// #include <zxing/ResultPoint.h>

namespace zxing {
namespace multi {
        
GenericMultipleBarcodeReader::GenericMultipleBarcodeReader(Reader& delegate)
    : delegate_(delegate) {}

GenericMultipleBarcodeReader::~GenericMultipleBarcodeReader(){}

vector<Ref<Result> > GenericMultipleBarcodeReader::decodeMultiple(Ref<BinaryBitmap> image,
                                                                  DecodeHints hints) {
  vector<Ref<Result> > results;
  doDecodeMultiple(image, hints, results, 0, 0, 0);
  if (results.empty()){
    throw ReaderException("No code detected");
  }
  return results;
}

void GenericMultipleBarcodeReader::doDecodeMultiple(Ref<BinaryBitmap> image,
                                                    DecodeHints hints,
                                                    vector<Ref<Result> >& results,
                                                    int xOffset,
                                                    int yOffset,
                                                    int currentDepth) {
  if (currentDepth > MAX_DEPTH) {
    return;
  }
  Ref<Result> result;
  try {
    result = delegate_.decode(image, hints);
  } catch (ReaderException const& ignored) {
    (void)ignored;
    return;
  }
  bool alreadyFound = false;
  for (unsigned int i = 0; i < results.size(); i++) {
    Ref<Result> existingResult = results[i];
    if (existingResult->getText()->getText() == result->getText()->getText()) {
      alreadyFound = true;
      break;
    }
  }
  if (!alreadyFound) {
    results.push_back(translateResultPoints(result, xOffset, yOffset));
  }

  ArrayRef< Ref<ResultPoint> > resultPoints = result->getResultPoints();
  if (resultPoints->empty()) {
    return;
  }

  int width = image->getWidth();
  int height = image->getHeight();
  float minX = float(width);
  float minY = float(height);
  float maxX = 0.0f;
  float maxY = 0.0f;
  for (int i = 0; i < resultPoints->size(); i++) {
    Ref<ResultPoint> point = resultPoints[i];
    float x = point->getX();
    float y = point->getY();
    if (x < minX) {
      minX = x;
    }
    if (y < minY) {
      minY = y;
    }
    if (x > maxX) {
      maxX = x;
    }
    if (y > maxY) {
      maxY = y;
    }
  }

  // Decode left of barcode
  if (minX > MIN_DIMENSION_TO_RECUR) {
    doDecodeMultiple(image->crop(0, 0, (int) minX, height),
                     hints, results, xOffset, yOffset, currentDepth+1);
  }
  // Decode above barcode
  if (minY > MIN_DIMENSION_TO_RECUR) {
    doDecodeMultiple(image->crop(0, 0, width, (int) minY),
                     hints, results, xOffset, yOffset, currentDepth+1);
  }
  // Decode right of barcode
  if (maxX < width - MIN_DIMENSION_TO_RECUR) {
    doDecodeMultiple(image->crop((int) maxX, 0, width - (int) maxX, height),
                     hints, results, xOffset + (int) maxX, yOffset, currentDepth+1);
  }
  // Decode below barcode
  if (maxY < height - MIN_DIMENSION_TO_RECUR) {
    doDecodeMultiple(image->crop(0, (int) maxY, width, height - (int) maxY),
                     hints, results, xOffset, yOffset + (int) maxY, currentDepth+1);
  }
}

Ref<Result> GenericMultipleBarcodeReader::translateResultPoints(Ref<Result> result, int xOffset, int yOffset){
    ArrayRef< Ref<ResultPoint> > oldResultPoints = result->getResultPoints();
  if (oldResultPoints->empty()) {
    return result;
  }
  ArrayRef< Ref<ResultPoint> > newResultPoints(new zxing::Array< Ref<ResultPoint> >());
  for (int i = 0; i < oldResultPoints->size(); i++) {
    Ref<ResultPoint> oldPoint = oldResultPoints[i];
    newResultPoints->values().push_back(Ref<ResultPoint>(new ResultPoint(oldPoint->getX() + xOffset, oldPoint->getY() + yOffset)));
  }
  return Ref<Result>(new Result(result->getText(), result->getRawBytes(), newResultPoints, result->getBarcodeFormat()));
}
}
}

// file: zxing/multi/MultipleBarcodeReader.cpp

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

namespace zxing {
namespace multi {

MultipleBarcodeReader::~MultipleBarcodeReader() { }

std::vector<Ref<Result> > MultipleBarcodeReader::decodeMultiple(Ref<BinaryBitmap> image) {
  return decodeMultiple(image, DecodeHints::DEFAULT_HINT);
}

} // End zxing::multi namespace
} // End zxing namespace

// file: zxing/multi/qrcode/QRCodeMultiReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/multi/qrcode/QRCodeMultiReader.h>
// #include <zxing/ReaderException.h>
// #include <zxing/multi/qrcode/detector/MultiDetector.h>
// #include <zxing/BarcodeFormat.h>

namespace zxing {
namespace multi {
QRCodeMultiReader::QRCodeMultiReader(){}

QRCodeMultiReader::~QRCodeMultiReader(){}

std::vector<Ref<Result> > QRCodeMultiReader::decodeMultiple(Ref<BinaryBitmap> image,
  DecodeHints hints)
{
  std::vector<Ref<Result> > results;
  MultiDetector detector(image->getBlackMatrix());

  std::vector<Ref<DetectorResult> > detectorResult =  detector.detectMulti(hints);
  for (unsigned int i = 0; i < detectorResult.size(); i++) {
    try {
      Ref<DecoderResult> decoderResult = getDecoder().decode(detectorResult[i]->getBits());
      ArrayRef< Ref<ResultPoint> > points = detectorResult[i]->getPoints();
      Ref<Result> result = Ref<Result>(new Result(decoderResult->getText(),
      decoderResult->getRawBytes(),
      points, BarcodeFormat::QR_CODE));
      // result->putMetadata(ResultMetadataType.BYTE_SEGMENTS, decoderResult->getByteSegments());
      // result->putMetadata(ResultMetadataType.ERROR_CORRECTION_LEVEL, decoderResult->getECLevel().toString());
      results.push_back(result);
    } catch (ReaderException const& re) {
      (void)re;
      // ignore and continue
    }
  }
  if (results.empty()){
    throw ReaderException("No code detected");
  }
  return results;
}

} // End zxing::multi namespace
} // End zxing namespace

// file: zxing/multi/qrcode/detector/MultiDetector.cpp

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

// #include <zxing/multi/qrcode/detector/MultiDetector.h>
// #include <zxing/multi/qrcode/detector/MultiFinderPatternFinder.h>
// #include <zxing/ReaderException.h>

namespace zxing {
namespace multi {
using namespace zxing::qrcode;

MultiDetector::MultiDetector(Ref<BitMatrix> image) : Detector(image) {}

MultiDetector::~MultiDetector(){}

std::vector<Ref<DetectorResult> > MultiDetector::detectMulti(DecodeHints hints){
  Ref<BitMatrix> image = getImage();
  MultiFinderPatternFinder finder = MultiFinderPatternFinder(image, hints.getResultPointCallback());
  std::vector<Ref<FinderPatternInfo> > info = finder.findMulti(hints);
  std::vector<Ref<DetectorResult> > result;
  for(unsigned int i = 0; i < info.size(); i++){
    try{
      result.push_back(processFinderPatternInfo(info[i]));
    } catch (ReaderException const& e){
      (void)e;
      // ignore
    }
  }

  return result;
}

} // End zxing::multi namespace
} // End zxing namespace

// file: zxing/multi/qrcode/detector/MultiFinderPatternFinder.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <cmath>
// #include <algorithm>
// #include <zxing/multi/qrcode/detector/MultiFinderPatternFinder.h>
// #include <zxing/DecodeHints.h>
// #include <zxing/ReaderException.h>

namespace zxing {
namespace multi {
        
const float MultiFinderPatternFinder::MAX_MODULE_COUNT_PER_EDGE = 180;
const float MultiFinderPatternFinder::MIN_MODULE_COUNT_PER_EDGE = 9;
const float MultiFinderPatternFinder::DIFF_MODSIZE_CUTOFF_PERCENT = 0.05f;
const float MultiFinderPatternFinder::DIFF_MODSIZE_CUTOFF = 0.5f;

namespace {

bool compareModuleSize(Ref<FinderPattern> a, Ref<FinderPattern> b){
  float value = a->getEstimatedModuleSize() - b->getEstimatedModuleSize();
  return value < 0.0;
}

}

MultiFinderPatternFinder::MultiFinderPatternFinder(Ref<BitMatrix> image,
                                                   Ref<ResultPointCallback> resultPointCallback)
    : FinderPatternFinder(image, resultPointCallback)
{
}

MultiFinderPatternFinder::~MultiFinderPatternFinder(){}

vector<Ref<FinderPatternInfo> > MultiFinderPatternFinder::findMulti(DecodeHints const& hints){
  bool tryHarder = hints.getTryHarder();
  Ref<BitMatrix> image = image_; // Protected member
  int maxI = image->getHeight();
  int maxJ = image->getWidth();
  // We are looking for black/white/black/white/black modules in
  // 1:1:3:1:1 ratio; this tracks the number of such modules seen so far

  // Let's assume that the maximum version QR Code we support takes up 1/4 the height of the
  // image, and then account for the center being 3 modules in size. This gives the smallest
  // number of pixels the center could be, so skip this often. When trying harder, look for all
  // QR versions regardless of how dense they are.
  int iSkip = (int) (maxI / (MAX_MODULES * 4.0f) * 3);
  if (iSkip < MIN_SKIP || tryHarder) {
    iSkip = MIN_SKIP;
  }

  int stateCount[5];
  for (int i = iSkip - 1; i < maxI; i += iSkip) {
    // Get a row of black/white values
    stateCount[0] = 0;
    stateCount[1] = 0;
    stateCount[2] = 0;
    stateCount[3] = 0;
    stateCount[4] = 0;
    int currentState = 0;
    for (int j = 0; j < maxJ; j++) {
      if (image->get(j, i)) {
        // Black pixel
        if ((currentState & 1) == 1) { // Counting white pixels
          currentState++;
        }
        stateCount[currentState]++;
      } else { // White pixel
        if ((currentState & 1) == 0) { // Counting black pixels
          if (currentState == 4) { // A winner?
            if (foundPatternCross(stateCount) && handlePossibleCenter(stateCount, i, j)) { // Yes
              // Clear state to start looking again
              currentState = 0;
              stateCount[0] = 0;
              stateCount[1] = 0;
              stateCount[2] = 0;
              stateCount[3] = 0;
              stateCount[4] = 0;
            } else { // No, shift counts back by two
              stateCount[0] = stateCount[2];
              stateCount[1] = stateCount[3];
              stateCount[2] = stateCount[4];
              stateCount[3] = 1;
              stateCount[4] = 0;
              currentState = 3;
            }
          } else {
            stateCount[++currentState]++;
          }
        } else { // Counting white pixels
          stateCount[currentState]++;
        }
      }
    } // for j=...

    if (foundPatternCross(stateCount)) {
      handlePossibleCenter(stateCount, i, maxJ);
    } // end if foundPatternCross
  } // for i=iSkip-1 ...
  vector<vector<Ref<FinderPattern> > > patternInfo = selectBestPatterns();
  vector<Ref<FinderPatternInfo> > result;
  for (unsigned int i = 0; i < patternInfo.size(); i++) {
    vector<Ref<FinderPattern> > pattern = patternInfo[i];
    pattern = FinderPatternFinder::orderBestPatterns(pattern);
    result.push_back(Ref<FinderPatternInfo>(new FinderPatternInfo(pattern)));
  }
  return result;
}

vector<vector<Ref<FinderPattern> > > MultiFinderPatternFinder::selectBestPatterns(){
  vector<Ref<FinderPattern> > possibleCenters = possibleCenters_;

  int size = (int)possibleCenters.size();

  if (size < 3) {
    // Couldn't find enough finder patterns
    throw ReaderException("No code detected");
  }

  vector<vector<Ref<FinderPattern> > > results;

  /*
   * Begin HE modifications to safely detect multiple codes of equal size
   */
  if (size == 3) {
    results.push_back(possibleCenters_);
    return results;
  }

  // Sort by estimated module size to speed up the upcoming checks
  //TODO do a sort based on module size
  sort(possibleCenters.begin(), possibleCenters.end(), compareModuleSize);

  /*
   * Now lets start: build a list of tuples of three finder locations that
   *  - feature similar module sizes
   *  - are placed in a distance so the estimated module count is within the QR specification
   *  - have similar distance between upper left/right and left top/bottom finder patterns
   *  - form a triangle with 90° angle (checked by comparing top right/bottom left distance
   *    with pythagoras)
   *
   * Note: we allow each point to be used for more than one code region: this might seem
   * counterintuitive at first, but the performance penalty is not that big. At this point,
   * we cannot make a good quality decision whether the three finders actually represent
   * a QR code, or are just by chance layouted so it looks like there might be a QR code there.
   * So, if the layout seems right, lets have the decoder try to decode.
   */

  for (int i1 = 0; i1 < (size - 2); i1++) {
    Ref<FinderPattern> p1 = possibleCenters[i1];
    for (int i2 = i1 + 1; i2 < (size - 1); i2++) {
      Ref<FinderPattern> p2 = possibleCenters[i2];
      // Compare the expected module sizes; if they are really off, skip
      float vModSize12 = (p1->getEstimatedModuleSize() - p2->getEstimatedModuleSize()) / min(p1->getEstimatedModuleSize(), p2->getEstimatedModuleSize());
      float vModSize12A = abs(p1->getEstimatedModuleSize() - p2->getEstimatedModuleSize());
      if (vModSize12A > DIFF_MODSIZE_CUTOFF && vModSize12 >= DIFF_MODSIZE_CUTOFF_PERCENT) {
        // break, since elements are ordered by the module size deviation there cannot be
        // any more interesting elements for the given p1.
        break;
      }
      for (int i3 = i2 + 1; i3 < size; i3++) {
        Ref<FinderPattern> p3 = possibleCenters[i3];
        // Compare the expected module sizes; if they are really off, skip
        float vModSize23 = (p2->getEstimatedModuleSize() - p3->getEstimatedModuleSize()) / min(p2->getEstimatedModuleSize(), p3->getEstimatedModuleSize());
        float vModSize23A = abs(p2->getEstimatedModuleSize() - p3->getEstimatedModuleSize());
        if (vModSize23A > DIFF_MODSIZE_CUTOFF && vModSize23 >= DIFF_MODSIZE_CUTOFF_PERCENT) {
          // break, since elements are ordered by the module size deviation there cannot be
          // any more interesting elements for the given p1.
          break;
        }
        vector<Ref<FinderPattern> > test;
        test.push_back(p1);
        test.push_back(p2);
        test.push_back(p3);
        test = FinderPatternFinder::orderBestPatterns(test);
        // Calculate the distances: a = topleft-bottomleft, b=topleft-topright, c = diagonal
        Ref<FinderPatternInfo> info = Ref<FinderPatternInfo>(new FinderPatternInfo(test));
        float dA = FinderPatternFinder::distance(info->getTopLeft(), info->getBottomLeft());
        float dC = FinderPatternFinder::distance(info->getTopRight(), info->getBottomLeft());
        float dB = FinderPatternFinder::distance(info->getTopLeft(), info->getTopRight());
        // Check the sizes
        float estimatedModuleCount = (dA + dB) / (p1->getEstimatedModuleSize() * 2.0f);
        if (estimatedModuleCount > MAX_MODULE_COUNT_PER_EDGE || estimatedModuleCount < MIN_MODULE_COUNT_PER_EDGE) {
          continue;
        }
        // Calculate the difference of the edge lengths in percent
        float vABBC = abs((dA - dB) / min(dA, dB));
        if (vABBC >= 0.1f) {
          continue;
        }
        // Calculate the diagonal length by assuming a 90° angle at topleft
        float dCpy = (float) sqrt(dA * dA + dB * dB);
        // Compare to the real distance in %
        float vPyC = abs((dC - dCpy) / min(dC, dCpy));
        if (vPyC >= 0.1f) {
          continue;
        }
        // All tests passed!
        results.push_back(test);
      } // end iterate p3
    } // end iterate p2
  } // end iterate p1
  if (results.empty()){
    // Nothing found!
    throw ReaderException("No code detected");
  }
  return results;
}
}
}

// file: zxing/oned/CodaBarReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/ZXing.h>
// #include <zxing/oned/CodaBarReader.h>
// #include <zxing/oned/OneDResultPoint.h>
// #include <zxing/common/Array.h>
// #include <zxing/ReaderException.h>
// #include <zxing/NotFoundException.h>
// #include <zxing/FormatException.h>
// #include <zxing/ChecksumException.h>
// #include <math.h>
// #include <sstream>

namespace zxing {
namespace oned {

namespace codabar {
  char const ALPHABET_STRING[] = "0123456789-$:/.+ABCD";
  char const* const ALPHABET = ALPHABET_STRING;

  /**
   * These represent the encodings of characters, as patterns of wide and narrow bars. The 7 least-significant bits of
   * each int correspond to the pattern of wide and narrow, with 1s representing "wide" and 0s representing narrow.
   */
  const int CHARACTER_ENCODINGS[] = {
    0x003, 0x006, 0x009, 0x060, 0x012, 0x042, 0x021, 0x024, 0x030, 0x048, // 0-9
    0x00c, 0x018, 0x045, 0x051, 0x054, 0x015, 0x01A, 0x029, 0x00B, 0x00E, // -$:/.+ABCD
  };

  // minimal number of characters that should be present (inclusing start and stop characters)
  // under normal circumstances this should be set to 3, but can be set higher
  // as a last-ditch attempt to reduce false positives.
  const int MIN_CHARACTER_LENGTH = 3;

  // official start and end patterns
  const char STARTEND_ENCODING[] = {'A', 'B', 'C', 'D', 0};
  // some codabar generator allow the codabar string to be closed by every
  // character. This will cause lots of false positives!

  // some industries use a checksum standard but this is not part of the original codabar standard
  // for more information see : http://www.mecsw.com/specs/codabar.html
}

// These values are critical for determining how permissive the decoding
// will be. All stripe sizes must be within the window these define, as
// compared to the average stripe size.
const int CodaBarReader::MAX_ACCEPTABLE =
  (int) (PATTERN_MATCH_RESULT_SCALE_FACTOR * 2.0f);
const int CodaBarReader::PADDING =
  (int) (PATTERN_MATCH_RESULT_SCALE_FACTOR * 1.5f);

CodaBarReader::CodaBarReader()
  : counters(80, 0), counterLength(0) {}

Ref<Result> CodaBarReader::decodeRow(int rowNumber, Ref<BitArray> row) {

  { // Arrays.fill(counters, 0);
    int size = (int)counters.size();
    counters.resize(0);
    counters.resize(size); }

  setCounters(row);
  int startOffset = findStartPattern();
  int nextStart = startOffset;

  decodeRowResult.clear();
  do {
    int charOffset = toNarrowWidePattern(nextStart);
    if (charOffset == -1) {
      throw NotFoundException();
    }
    // Hack: We store the position in the alphabet table into a
    // StringBuilder, so that we can access the decoded patterns in
    // validatePattern. We'll translate to the actual characters later.
    decodeRowResult.append(1, (char)charOffset);
    nextStart += 8;
    // Stop as soon as we see the end character.
    if (decodeRowResult.length() > 1 &&
        arrayContains(codabar::STARTEND_ENCODING, codabar::ALPHABET[charOffset])) {
      break;
    }
  } while (nextStart < counterLength); // no fixed end pattern so keep on reading while data is available

  // Look for whitespace after pattern:
  int trailingWhitespace = counters[nextStart - 1];
  int lastPatternSize = 0;
  for (int i = -8; i < -1; i++) {
    lastPatternSize += counters[nextStart + i];
  }

  // We need to see whitespace equal to 50% of the last pattern size,
  // otherwise this is probably a false positive. The exception is if we are
  // at the end of the row. (I.e. the barcode barely fits.)
  if (nextStart < counterLength && trailingWhitespace < lastPatternSize / 2) {
    throw NotFoundException();
  }

  validatePattern(startOffset);

  // Translate character table offsets to actual characters.
  for (int i = 0; i < (int)decodeRowResult.length(); i++) {
      decodeRowResult[i] = codabar::ALPHABET[(int)decodeRowResult[i]];
  }
  // Ensure a valid start and end character
  char startchar = decodeRowResult[0];
  if (!arrayContains(codabar::STARTEND_ENCODING, startchar)) {
    throw NotFoundException();
  }
  char endchar = decodeRowResult[decodeRowResult.length() - 1];
  if (!arrayContains(codabar::STARTEND_ENCODING, endchar)) {
    throw NotFoundException();
  }

  // remove stop/start characters character and check if a long enough string is contained
  if ((int)decodeRowResult.length() <= codabar::MIN_CHARACTER_LENGTH) {
    // Almost surely a false positive ( start + stop + at least 1 character)
    throw NotFoundException();
  }

  decodeRowResult.erase(decodeRowResult.length() - 1, 1);
  decodeRowResult.erase(0, 1);

  int runningCount = 0;
  for (int i = 0; i < startOffset; i++) {
    runningCount += counters[i];
  }
  float left = (float) runningCount;
  for (int i = startOffset; i < nextStart - 1; i++) {
    runningCount += counters[i];
  }
  float right = (float) runningCount;

  ArrayRef< Ref<ResultPoint> > resultPoints(2);
  resultPoints[0] =
    Ref<OneDResultPoint>(new OneDResultPoint(left, (float) rowNumber));
  resultPoints[1] =
    Ref<OneDResultPoint>(new OneDResultPoint(right, (float) rowNumber));

  return Ref<Result>(new Result(Ref<String>(new String(decodeRowResult)),
                                ArrayRef<char>(),
                                resultPoints,
                                BarcodeFormat::CODABAR));
}

void CodaBarReader::validatePattern(int start)  {
  // First, sum up the total size of our four categories of stripe sizes;
  vector<int> sizes (4, 0);
  vector<int> counts (4, 0);
  int end = (int)decodeRowResult.length() - 1;

  // We break out of this loop in the middle, in order to handle
  // inter-character spaces properly.
  int pos = start;
  for (int i = 0; true; i++) {
    int pattern = codabar::CHARACTER_ENCODINGS[(int)decodeRowResult[i]];
    for (int j = 6; j >= 0; j--) {
      // Even j = bars, while odd j = spaces. Categories 2 and 3 are for
      // long stripes, while 0 and 1 are for short stripes.
      int category = (j & 1) + (pattern & 1) * 2;
      sizes[category] += counters[pos + j];
      counts[category]++;
      pattern >>= 1;
    }
    if (i >= end) {
      break;
    }
    // We ignore the inter-character space - it could be of any size.
    pos += 8;
  }

  // Calculate our allowable size thresholds using fixed-point math.
  vector<int> maxes (4, 0);
  vector<int> mins (4, 0);
  // Define the threshold of acceptability to be the midpoint between the
  // average small stripe and the average large stripe. No stripe lengths
  // should be on the "wrong" side of that line.
  for (int i = 0; i < 2; i++) {
    mins[i] = 0;  // Accept arbitrarily small "short" stripes.
    mins[i + 2] = ((sizes[i] << INTEGER_MATH_SHIFT) / counts[i] +
                   (sizes[i + 2] << INTEGER_MATH_SHIFT) / counts[i + 2]) >> 1;
    maxes[i] = mins[i + 2];
    maxes[i + 2] = (sizes[i + 2] * MAX_ACCEPTABLE + PADDING) / counts[i + 2];
  }

  // Now verify that all of the stripes are within the thresholds.
  pos = start;
  for (int i = 0; true; i++) {
    int pattern = codabar::CHARACTER_ENCODINGS[(int)decodeRowResult[i]];
    for (int j = 6; j >= 0; j--) {
      // Even j = bars, while odd j = spaces. Categories 2 and 3 are for
      // long stripes, while 0 and 1 are for short stripes.
      int category = (j & 1) + (pattern & 1) * 2;
      int size = counters[pos + j] << INTEGER_MATH_SHIFT;
      if (size < mins[category] || size > maxes[category]) {
        throw NotFoundException();
      }
      pattern >>= 1;
    }
    if (i >= end) {
      break;
    }
    pos += 8;
  }
}

/**
 * Records the size of all runs of white and black pixels, starting with white.
 * This is just like recordPattern, except it records all the counters, and
 * uses our builtin "counters" member for storage.
 * @param row row to count from
 */
void CodaBarReader::setCounters(Ref<BitArray> row)  {
  counterLength = 0;
  // Start from the first white bit.
  int i = row->getNextUnset(0);
  int end = row->getSize();
  if (i >= end) {
    throw NotFoundException();
  }
  bool isWhite = true;
  int count = 0;
  for (; i < end; i++) {
    if (row->get(i) ^ isWhite) { // that is, exactly one is true
      count++;
    } else {
      counterAppend(count);
      count = 1;
      isWhite = !isWhite;
    }
  }
  counterAppend(count);
}

void CodaBarReader::counterAppend(int e) {
  if (counterLength < (int)counters.size()) {
    counters[counterLength] = e;
  } else {
    counters.push_back(e);
  }
  counterLength++;
}

int CodaBarReader::findStartPattern() {
  for (int i = 1; i < counterLength; i += 2) {
    int charOffset = toNarrowWidePattern(i);
    if (charOffset != -1 && arrayContains(codabar::STARTEND_ENCODING, codabar::ALPHABET[charOffset])) {
      // Look for whitespace before start pattern, >= 50% of width of start pattern
      // We make an exception if the whitespace is the first element.
      int patternSize = 0;
      for (int j = i; j < i + 7; j++) {
        patternSize += counters[j];
      }
      if (i == 1 || counters[i-1] >= patternSize / 2) {
        return i;
      }
    }
  }
  throw NotFoundException();
}

bool CodaBarReader::arrayContains(char const array[], char key) {
  return strchr(array, key) != 0;
}


int CodaBarReader::toNarrowWidePattern(int position) {
  int end = position + 7;
  if (end >= counterLength) {
    return -1;
  }

  vector<int>& theCounters = counters;

  int maxBar = 0;
  int minBar = std::numeric_limits<int>::max();
  for (int j = position; j < end; j += 2) {
    int currentCounter = theCounters[j];
    if (currentCounter < minBar) {
      minBar = currentCounter;
    }
    if (currentCounter > maxBar) {
      maxBar = currentCounter;
    }
  }
  int thresholdBar = (minBar + maxBar) / 2;

  int maxSpace = 0;
  int minSpace = std::numeric_limits<int>::max();
  for (int j = position + 1; j < end; j += 2) {
    int currentCounter = theCounters[j];
    if (currentCounter < minSpace) {
      minSpace = currentCounter;
    }
    if (currentCounter > maxSpace) {
      maxSpace = currentCounter;
    }
  }
  int thresholdSpace = (minSpace + maxSpace) / 2;

  int bitmask = 1 << 7;
  int pattern = 0;
  for (int i = 0; i < 7; i++) {
    int threshold = (i & 1) == 0 ? thresholdBar : thresholdSpace;
    bitmask >>= 1;
    if (theCounters[position + i] > threshold) {
      pattern |= bitmask;
    }
  }

  for (int i = 0; i < ZXING_ARRAY_LEN(codabar::CHARACTER_ENCODINGS); i++) {
    if (codabar::CHARACTER_ENCODINGS[i] == pattern) {
      return i;
    }
  }
  return -1;
}
}
}

// file: zxing/oned/Code128Reader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/ZXing.h>
// #include <zxing/oned/Code128Reader.h>
// #include <zxing/oned/OneDResultPoint.h>
// #include <zxing/common/Array.h>
// #include <zxing/ReaderException.h>
// #include <zxing/NotFoundException.h>
// #include <zxing/FormatException.h>
// #include <zxing/ChecksumException.h>
// #include <math.h>
// #include <string.h>
// #include <sstream>
// #include <algorithm>  // vs12, std::min und std:max

namespace zxing {
namespace oned {

const int Code128Reader::MAX_AVG_VARIANCE = int(PATTERN_MATCH_RESULT_SCALE_FACTOR * 250/1000);
const int Code128Reader::MAX_INDIVIDUAL_VARIANCE = int(PATTERN_MATCH_RESULT_SCALE_FACTOR * 700/1000);

namespace {

const int CODE_SHIFT = 98;

const int CODE_CODE_C = 99;
const int CODE_CODE_B = 100;
const int CODE_CODE_A = 101;

const int CODE_FNC_1 = 102;
const int CODE_FNC_2 = 97;
const int CODE_FNC_3 = 96;
const int CODE_FNC_4_A = 101;
const int CODE_FNC_4_B = 100;

const int CODE_START_A = 103;
const int CODE_START_B = 104;
const int CODE_START_C = 105;
const int CODE_STOP = 106;

const int CODE_PATTERNS_LENGTH = 107;
const int CODE_PATTERNS[CODE_PATTERNS_LENGTH][6] = {
  {2, 1, 2, 2, 2, 2}, /* 0 */
  {2, 2, 2, 1, 2, 2},
  {2, 2, 2, 2, 2, 1},
  {1, 2, 1, 2, 2, 3},
  {1, 2, 1, 3, 2, 2},
  {1, 3, 1, 2, 2, 2}, /* 5 */
  {1, 2, 2, 2, 1, 3},
  {1, 2, 2, 3, 1, 2},
  {1, 3, 2, 2, 1, 2},
  {2, 2, 1, 2, 1, 3},
  {2, 2, 1, 3, 1, 2}, /* 10 */
  {2, 3, 1, 2, 1, 2},
  {1, 1, 2, 2, 3, 2},
  {1, 2, 2, 1, 3, 2},
  {1, 2, 2, 2, 3, 1},
  {1, 1, 3, 2, 2, 2}, /* 15 */
  {1, 2, 3, 1, 2, 2},
  {1, 2, 3, 2, 2, 1},
  {2, 2, 3, 2, 1, 1},
  {2, 2, 1, 1, 3, 2},
  {2, 2, 1, 2, 3, 1}, /* 20 */
  {2, 1, 3, 2, 1, 2},
  {2, 2, 3, 1, 1, 2},
  {3, 1, 2, 1, 3, 1},
  {3, 1, 1, 2, 2, 2},
  {3, 2, 1, 1, 2, 2}, /* 25 */
  {3, 2, 1, 2, 2, 1},
  {3, 1, 2, 2, 1, 2},
  {3, 2, 2, 1, 1, 2},
  {3, 2, 2, 2, 1, 1},
  {2, 1, 2, 1, 2, 3}, /* 30 */
  {2, 1, 2, 3, 2, 1},
  {2, 3, 2, 1, 2, 1},
  {1, 1, 1, 3, 2, 3},
  {1, 3, 1, 1, 2, 3},
  {1, 3, 1, 3, 2, 1}, /* 35 */
  {1, 1, 2, 3, 1, 3},
  {1, 3, 2, 1, 1, 3},
  {1, 3, 2, 3, 1, 1},
  {2, 1, 1, 3, 1, 3},
  {2, 3, 1, 1, 1, 3}, /* 40 */
  {2, 3, 1, 3, 1, 1},
  {1, 1, 2, 1, 3, 3},
  {1, 1, 2, 3, 3, 1},
  {1, 3, 2, 1, 3, 1},
  {1, 1, 3, 1, 2, 3}, /* 45 */
  {1, 1, 3, 3, 2, 1},
  {1, 3, 3, 1, 2, 1},
  {3, 1, 3, 1, 2, 1},
  {2, 1, 1, 3, 3, 1},
  {2, 3, 1, 1, 3, 1}, /* 50 */
  {2, 1, 3, 1, 1, 3},
  {2, 1, 3, 3, 1, 1},
  {2, 1, 3, 1, 3, 1},
  {3, 1, 1, 1, 2, 3},
  {3, 1, 1, 3, 2, 1}, /* 55 */
  {3, 3, 1, 1, 2, 1},
  {3, 1, 2, 1, 1, 3},
  {3, 1, 2, 3, 1, 1},
  {3, 3, 2, 1, 1, 1},
  {3, 1, 4, 1, 1, 1}, /* 60 */
  {2, 2, 1, 4, 1, 1},
  {4, 3, 1, 1, 1, 1},
  {1, 1, 1, 2, 2, 4},
  {1, 1, 1, 4, 2, 2},
  {1, 2, 1, 1, 2, 4}, /* 65 */
  {1, 2, 1, 4, 2, 1},
  {1, 4, 1, 1, 2, 2},
  {1, 4, 1, 2, 2, 1},
  {1, 1, 2, 2, 1, 4},
  {1, 1, 2, 4, 1, 2}, /* 70 */
  {1, 2, 2, 1, 1, 4},
  {1, 2, 2, 4, 1, 1},
  {1, 4, 2, 1, 1, 2},
  {1, 4, 2, 2, 1, 1},
  {2, 4, 1, 2, 1, 1}, /* 75 */
  {2, 2, 1, 1, 1, 4},
  {4, 1, 3, 1, 1, 1},
  {2, 4, 1, 1, 1, 2},
  {1, 3, 4, 1, 1, 1},
  {1, 1, 1, 2, 4, 2}, /* 80 */
  {1, 2, 1, 1, 4, 2},
  {1, 2, 1, 2, 4, 1},
  {1, 1, 4, 2, 1, 2},
  {1, 2, 4, 1, 1, 2},
  {1, 2, 4, 2, 1, 1}, /* 85 */
  {4, 1, 1, 2, 1, 2},
  {4, 2, 1, 1, 1, 2},
  {4, 2, 1, 2, 1, 1},
  {2, 1, 2, 1, 4, 1},
  {2, 1, 4, 1, 2, 1}, /* 90 */
  {4, 1, 2, 1, 2, 1},
  {1, 1, 1, 1, 4, 3},
  {1, 1, 1, 3, 4, 1},
  {1, 3, 1, 1, 4, 1},
  {1, 1, 4, 1, 1, 3}, /* 95 */
  {1, 1, 4, 3, 1, 1},
  {4, 1, 1, 1, 1, 3},
  {4, 1, 1, 3, 1, 1},
  {1, 1, 3, 1, 4, 1},
  {1, 1, 4, 1, 3, 1}, /* 100 */
  {3, 1, 1, 1, 4, 1},
  {4, 1, 1, 1, 3, 1},
  {2, 1, 1, 4, 1, 2},
  {2, 1, 1, 2, 1, 4},
  {2, 1, 1, 2, 3, 2}, /* 105 */
  {2, 3, 3, 1, 1, 1}
};

}

Code128Reader::Code128Reader(){}

vector<int> Code128Reader::findStartPattern(Ref<BitArray> row){
  int width = row->getSize();
  int rowOffset = row->getNextSet(0);

  int counterPosition = 0;
  vector<int> counters (6, 0);
  int patternStart = rowOffset;
  bool isWhite = false;
  int patternLength =  (int)counters.size();

  for (int i = rowOffset; i < width; i++) {
    if (row->get(i) ^ isWhite) {
      counters[counterPosition]++;
    } else {
      if (counterPosition == patternLength - 1) {
        int bestVariance = MAX_AVG_VARIANCE;
        int bestMatch = -1;
        for (int startCode = CODE_START_A; startCode <= CODE_START_C; startCode++) {
          int variance = patternMatchVariance(counters, CODE_PATTERNS[startCode], MAX_INDIVIDUAL_VARIANCE);
          if (variance < bestVariance) {
            bestVariance = variance;
            bestMatch = startCode;
          }
        }
        // Look for whitespace before start pattern, >= 50% of width of start pattern
        if (bestMatch >= 0 &&
            row->isRange(std::max(0, patternStart - (i - patternStart) / 2), patternStart, false)) {
          vector<int> resultValue (3, 0);
          resultValue[0] = patternStart;
          resultValue[1] = i;
          resultValue[2] = bestMatch;
          return resultValue;
        }
        patternStart += counters[0] + counters[1];
        for (int y = 2; y < patternLength; y++) {
          counters[y - 2] = counters[y];
        }
        counters[patternLength - 2] = 0;
        counters[patternLength - 1] = 0;
        counterPosition--;
      } else {
        counterPosition++;
      }
      counters[counterPosition] = 1;
      isWhite = !isWhite;
    }
  }
  throw NotFoundException();
}

int Code128Reader::decodeCode(Ref<BitArray> row, vector<int>& counters, int rowOffset) {
  recordPattern(row, rowOffset, counters);
  int bestVariance = MAX_AVG_VARIANCE; // worst variance we'll accept
  int bestMatch = -1;
  for (int d = 0; d < CODE_PATTERNS_LENGTH; d++) {
    int const* const pattern = CODE_PATTERNS[d];
    int variance = patternMatchVariance(counters, pattern, MAX_INDIVIDUAL_VARIANCE);
    if (variance < bestVariance) {
      bestVariance = variance;
      bestMatch = d;
    }
  }
  // TODO We're overlooking the fact that the STOP pattern has 7 values, not 6.
  if (bestMatch >= 0) {
    return bestMatch;
  } else {
    throw NotFoundException();
  }
}

Ref<Result> Code128Reader::decodeRow(int rowNumber, Ref<BitArray> row) {
  // boolean convertFNC1 = hints != null && hints.containsKey(DecodeHintType.ASSUME_GS1);
  boolean convertFNC1 = false;
  vector<int> startPatternInfo (findStartPattern(row));
  int startCode = startPatternInfo[2];
  int codeSet;
  switch (startCode) {
    case CODE_START_A:
      codeSet = CODE_CODE_A;
      break;
    case CODE_START_B:
      codeSet = CODE_CODE_B;
      break;
    case CODE_START_C:
      codeSet = CODE_CODE_C;
      break;
    default:
      throw FormatException();
  }

  bool done = false;
  bool isNextShifted = false;

  string result;
  vector<char> rawCodes(20, 0);

  int lastStart = startPatternInfo[0];
  int nextStart = startPatternInfo[1];
  vector<int> counters (6, 0);

  int lastCode = 0;
  int code = 0;
  int checksumTotal = startCode;
  int multiplier = 0;
  bool lastCharacterWasPrintable = true;

  std::ostringstream oss;

  while (!done) {

    bool unshift = isNextShifted;
    isNextShifted = false;

    // Save off last code
    lastCode = code;

    code = decodeCode(row, counters, nextStart);

    // Remember whether the last code was printable or not (excluding CODE_STOP)
    if (code != CODE_STOP) {
      lastCharacterWasPrintable = true;
    }

    // Add to checksum computation (if not CODE_STOP of course)
    if (code != CODE_STOP) {
      multiplier++;
      checksumTotal += multiplier * code;
    }

    // Advance to where the next code will to start
    lastStart = nextStart;
    for (unsigned long i = 0, e = counters.size(); i < e; i++) {
      nextStart += counters[i];
    }

    // Take care of illegal start codes
    switch (code) {
      case CODE_START_A:
      case CODE_START_B:
      case CODE_START_C:
        throw FormatException();
    }

    switch (codeSet) {

      case CODE_CODE_A:
        if (code < 64) {
          result.append(1, (char) (' ' + code));
        } else if (code < 96) {
          result.append(1, (char) (code - 64));
        } else {
          // Don't let CODE_STOP, which always appears, affect whether whether we think the
          // last code was printable or not.
          if (code != CODE_STOP) {
            lastCharacterWasPrintable = false;
          }
          switch (code) {
            case CODE_FNC_1:
              if (convertFNC1) {
                if (result.length() == 0){
                  // GS1 specification 5.4.3.7. and 5.4.6.4. If the first char after the start code
                  // is FNC1 then this is GS1-128. We add the symbology identifier.
                  result.append("]C1");
                } else {
                  // GS1 specification 5.4.7.5. Every subsequent FNC1 is returned as ASCII 29 (GS)
                  result.append(1, (char) 29);
                }
              }
              break;
            case CODE_FNC_2:
            case CODE_FNC_3:
            case CODE_FNC_4_A:
              // do nothing?
              break;
            case CODE_SHIFT:
              isNextShifted = true;
              codeSet = CODE_CODE_B;
              break;
            case CODE_CODE_B:
              codeSet = CODE_CODE_B;
              break;
            case CODE_CODE_C:
              codeSet = CODE_CODE_C;
              break;
            case CODE_STOP:
              done = true;
              break;
          }
        }
        break;
      case CODE_CODE_B:
        if (code < 96) {
          result.append(1, (char) (' ' + code));
        } else {
          if (code != CODE_STOP) {
            lastCharacterWasPrintable = false;
          }
          switch (code) {
            case CODE_FNC_1:
            case CODE_FNC_2:
            case CODE_FNC_3:
            case CODE_FNC_4_B:
              // do nothing?
              break;
            case CODE_SHIFT:
              isNextShifted = true;
              codeSet = CODE_CODE_A;
              break;
            case CODE_CODE_A:
              codeSet = CODE_CODE_A;
              break;
            case CODE_CODE_C:
              codeSet = CODE_CODE_C;
              break;
            case CODE_STOP:
              done = true;
              break;
          }
        }
        break;
      case CODE_CODE_C:
        if (code < 100) {
          if (code < 10) {
            result.append(1, '0');
          }
          oss.clear();
          oss.str("");
          oss << code;
          result.append(oss.str());
        } else {
          if (code != CODE_STOP) {
            lastCharacterWasPrintable = false;
          }
          switch (code) {
            case CODE_FNC_1:
              // do nothing?
              break;
            case CODE_CODE_A:
              codeSet = CODE_CODE_A;
              break;
            case CODE_CODE_B:
              codeSet = CODE_CODE_B;
              break;
            case CODE_STOP:
              done = true;
              break;
          }
        }
        break;
    }

    // Unshift back to another code set if we were shifted
    if (unshift) {
      codeSet = codeSet == CODE_CODE_A ? CODE_CODE_B : CODE_CODE_A;
    }

  }

  int lastPatternSize = nextStart - lastStart;

  // Check for ample whitespace following pattern, but, to do this we first need to remember that
  // we fudged decoding CODE_STOP since it actually has 7 bars, not 6. There is a black bar left
  // to read off. Would be slightly better to properly read. Here we just skip it:
  nextStart = row->getNextUnset(nextStart);
  if (!row->isRange(nextStart,
                    std::min(row->getSize(), nextStart + (nextStart - lastStart) / 2),
                    false)) {
    throw NotFoundException();
  }

  // Pull out from sum the value of the penultimate check code
  checksumTotal -= multiplier * lastCode;
  // lastCode is the checksum then:
  if (checksumTotal % 103 != lastCode) {
    throw ChecksumException();
  }

  // Need to pull out the check digits from string
  int resultLength = (int)result.length();
  if (resultLength == 0) {
    // false positive
    throw NotFoundException();
  }

  // Only bother if the result had at least one character, and if the checksum digit happened to
  // be a printable character. If it was just interpreted as a control code, nothing to remove.
  if (resultLength > 0 && lastCharacterWasPrintable) {
    if (codeSet == CODE_CODE_C) {
      result.erase(resultLength - 2, resultLength);
    } else {
      result.erase(resultLength - 1, resultLength);
    }
  }

  float left = (float) (startPatternInfo[1] + startPatternInfo[0]) / 2.0f;
  float right = lastStart + lastPatternSize / 2.0f;

  int rawCodesSize = (int)rawCodes.size();
  ArrayRef<char> rawBytes (rawCodesSize);
  for (int i = 0; i < rawCodesSize; i++) {
    rawBytes[i] = rawCodes[i];
  }

  ArrayRef< Ref<ResultPoint> > resultPoints(2);
  resultPoints[0] =
      Ref<OneDResultPoint>(new OneDResultPoint(left, (float) rowNumber));
  resultPoints[1] =
      Ref<OneDResultPoint>(new OneDResultPoint(right, (float) rowNumber));

  return Ref<Result>(new Result(Ref<String>(new String(result)), rawBytes, resultPoints,
                                BarcodeFormat::CODE_128));
}

Code128Reader::~Code128Reader(){}

zxing::BarcodeFormat Code128Reader::getBarcodeFormat(){
  return BarcodeFormat::CODE_128;
}
}
}

// file: zxing/oned/Code39Reader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include "Code39Reader.h"
// #include <zxing/oned/OneDResultPoint.h>
// #include <zxing/common/Array.h>
// #include <zxing/ReaderException.h>
// #include <zxing/NotFoundException.h>
// #include <zxing/ChecksumException.h>
// #include <math.h>
// #include <limits.h>
// #include <algorithm>  // vs12, std::min und std:max

namespace zxing {
namespace oned {
namespace code39 {
    
  const char* ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ-. *$/+%";

  /**
   * These represent the encodings of characters, as patterns of wide and narrow
   * bars.
   * The 9 least-significant bits of each int correspond to the pattern of wide
   * and narrow, with 1s representing "wide" and 0s representing narrow.
   */
  const int CHARACTER_ENCODINGS_LEN = 44;
  int CHARACTER_ENCODINGS[CHARACTER_ENCODINGS_LEN] = {
    0x034, 0x121, 0x061, 0x160, 0x031, 0x130, 0x070, 0x025, 0x124, 0x064, // 0-9
    0x109, 0x049, 0x148, 0x019, 0x118, 0x058, 0x00D, 0x10C, 0x04C, 0x01C, // A-J
    0x103, 0x043, 0x142, 0x013, 0x112, 0x052, 0x007, 0x106, 0x046, 0x016, // K-T
    0x181, 0x0C1, 0x1C0, 0x091, 0x190, 0x0D0, 0x085, 0x184, 0x0C4, 0x094, // U-*
    0x0A8, 0x0A2, 0x08A, 0x02A // $-%
  };

  int ASTERISK_ENCODING = 0x094;
  const char* ALPHABET_STRING =
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ-. *$/+%";

  std::string alphabet_string (ALPHABET_STRING);
}

void Code39Reader::init(bool usingCheckDigit_, bool extendedMode_) {
  usingCheckDigit = usingCheckDigit_;
  extendedMode = extendedMode_;
  decodeRowResult.reserve(20);
  counters.resize(9);
}

/**
 * Creates a reader that assumes all encoded data is data, and does not treat
 * the final character as a check digit. It will not decoded "extended
 * Code 39" sequences.
 */
Code39Reader::Code39Reader() {
  init();
}

/**
 * Creates a reader that can be configured to check the last character as a
 * check digit. It will not decoded "extended Code 39" sequences.
 *
 * @param usingCheckDigit if true, treat the last data character as a check
 * digit, not data, and verify that the checksum passes.
 */
Code39Reader::Code39Reader(bool usingCheckDigit_) {
  init(usingCheckDigit_);
}

Code39Reader::Code39Reader(bool usingCheckDigit_, bool extendedMode_) {
  init(usingCheckDigit_, extendedMode_);
}

Ref<Result> Code39Reader::decodeRow(int rowNumber, Ref<BitArray> row) {
  std::vector<int>& theCounters (counters);
  { // Arrays.fill(counters, 0);
    unsigned long size = theCounters.size();
    theCounters.resize(0);
    theCounters.resize(size); }
  std::string& result (decodeRowResult);
  result.clear();

  vector<int> start (findAsteriskPattern(row, theCounters));
  // Read off white space
  int nextStart = row->getNextSet(start[1]);
  int end = row->getSize();

  char decodedChar;
  int lastStart;
  do {
    recordPattern(row, nextStart, theCounters);
    int pattern = toNarrowWidePattern(theCounters);
    if (pattern < 0) {
      throw NotFoundException();;
    }
    decodedChar = patternToChar(pattern);
    result.append(1, decodedChar);
    lastStart = nextStart;
    for (unsigned long i = 0, end=theCounters.size(); i < end; i++) {
      nextStart += theCounters[i];
    }
    // Read off white space
    nextStart = row->getNextSet(nextStart);
  } while (decodedChar != '*');
  result.resize(decodeRowResult.length()-1);// remove asterisk

    // Look for whitespace after pattern:
  int lastPatternSize = 0;
  for (unsigned long i = 0, e = theCounters.size(); i < e; i++) {
    lastPatternSize += theCounters[i];
  }
  int whiteSpaceAfterEnd = nextStart - lastStart - lastPatternSize;
  // If 50% of last pattern size, following last pattern, is not whitespace,
  // fail (but if it's whitespace to the very end of the image, that's OK)
  if (nextStart != end && (whiteSpaceAfterEnd >> 1) < lastPatternSize) {
    throw NotFoundException();
  }

  if (usingCheckDigit) {
    int max = (int)result.length() - 1;
    int total = 0;
    for (int i = 0; i < max; i++) {
        total += code39::alphabet_string.find_first_of(decodeRowResult[i], 0);
    }
    if (result[max] != code39::ALPHABET[total % 43]) {
      throw ChecksumException();
    }
    result.resize(max);
  }

  if (result.length() == 0) {
    // Almost false positive
    throw NotFoundException();
  }

  Ref<String> resultString;
  if (extendedMode) {
    resultString = decodeExtended(result);
  } else {
    resultString = Ref<String>(new String(result));
  }

  float left = (float) (start[1] + start[0]) / 2.0f;
  float right = lastStart + lastPatternSize / 2.0f;

  ArrayRef< Ref<ResultPoint> > resultPoints (2);
  resultPoints[0] =
    Ref<OneDResultPoint>(new OneDResultPoint(left, (float) rowNumber));
  resultPoints[1] =
    Ref<OneDResultPoint>(new OneDResultPoint(right, (float) rowNumber));

  return Ref<Result>(
    new Result(resultString, ArrayRef<char>(), resultPoints, BarcodeFormat::CODE_39)
    );
}

vector<int> Code39Reader::findAsteriskPattern(Ref<BitArray> row, vector<int>& counters){
  int width = row->getSize();
  int rowOffset = row->getNextSet(0);

  int counterPosition = 0;
  int patternStart = rowOffset;
  bool isWhite = false;
  unsigned long patternLength = counters.size();

  for (int i = rowOffset; i < width; i++) {
    if (row->get(i) ^ isWhite) {
      counters[counterPosition]++;
    } else {
      if (counterPosition == patternLength - 1) {
        // Look for whitespace before start pattern, >= 50% of width of
        // start pattern.
        if (toNarrowWidePattern(counters) == code39::ASTERISK_ENCODING &&
            row->isRange(std::max(0, patternStart - ((i - patternStart) >> 1)), patternStart, false)) {
          vector<int> resultValue (2, 0);
          resultValue[0] = patternStart;
          resultValue[1] = i;
          return resultValue;
        }
        patternStart += counters[0] + counters[1];
        for (int y = 2; y < patternLength; y++) {
          counters[y - 2] = counters[y];
        }
        counters[patternLength - 2] = 0;
        counters[patternLength - 1] = 0;
        counterPosition--;
      } else {
        counterPosition++;
      }
      counters[counterPosition] = 1;
      isWhite = !isWhite;
    }
  }
  throw NotFoundException();
}

// For efficiency, returns -1 on failure. Not throwing here saved as many as
// 700 exceptions per image when using some of our blackbox images.
int Code39Reader::toNarrowWidePattern(vector<int>& counters){
  unsigned long numCounters = counters.size();
  int maxNarrowCounter = 0;
  int wideCounters;
  do {
    int minCounter = INT_MAX;
    for (int i = 0; i < numCounters; i++) {
      int counter = counters[i];
      if (counter < minCounter && counter > maxNarrowCounter) {
        minCounter = counter;
      }
    }
    maxNarrowCounter = minCounter;
    wideCounters = 0;
    int totalWideCountersWidth = 0;
    int pattern = 0;
    for (int i = 0; i < numCounters; i++) {
      int counter = counters[i];
      if (counters[i] > maxNarrowCounter) {
        pattern |= 1 << (numCounters - 1 - i);
        wideCounters++;
        totalWideCountersWidth += counter;
      }
    }
    if (wideCounters == 3) {
      // Found 3 wide counters, but are they close enough in width?
      // We can perform a cheap, conservative check to see if any individual
      // counter is more than 1.5 times the average:
      for (int i = 0; i < numCounters && wideCounters > 0; i++) {
        int counter = counters[i];
        if (counters[i] > maxNarrowCounter) {
          wideCounters--;
          // totalWideCountersWidth = 3 * average, so this checks if
          // counter >= 3/2 * average.
          if ((counter << 1) >= totalWideCountersWidth) {
            return -1;
          }
        }
      }
      return pattern;
    }
  } while (wideCounters > 3);
  return -1;
}

char Code39Reader::patternToChar(int pattern){
  for (int i = 0; i < code39::CHARACTER_ENCODINGS_LEN; i++) {
    if (code39::CHARACTER_ENCODINGS[i] == pattern) {
      return code39::ALPHABET[i];
    }
  }
  throw ReaderException("");
}

Ref<String> Code39Reader::decodeExtended(std::string encoded){
  int length = (int)encoded.length();
  std::string tmpDecoded;
  for (int i = 0; i < length; i++) {
    char c = encoded[i];
    if (c == '+' || c == '$' || c == '%' || c == '/') {
      char next = encoded[i + 1];
      char decodedChar = '\0';
      switch (c) {
      case '+':
        // +A to +Z map to a to z
        if (next >= 'A' && next <= 'Z') {
          decodedChar = (char) (next + 32);
        } else {
          throw ReaderException("");
        }
        break;
      case '$':
        // $A to $Z map to control codes SH to SB
        if (next >= 'A' && next <= 'Z') {
          decodedChar = (char) (next - 64);
        } else {
          throw ReaderException("");
        }
        break;
      case '%':
        // %A to %E map to control codes ESC to US
        if (next >= 'A' && next <= 'E') {
          decodedChar = (char) (next - 38);
        } else if (next >= 'F' && next <= 'W') {
          decodedChar = (char) (next - 11);
        } else {
          throw ReaderException("");
        }
        break;
      case '/':
        // /A to /O map to ! to , and /Z maps to :
        if (next >= 'A' && next <= 'O') {
          decodedChar = (char) (next - 32);
        } else if (next == 'Z') {
          decodedChar = ':';
        } else {
          throw ReaderException("");
        }
        break;
      }
      tmpDecoded.append(1, decodedChar);
      // bump up i again since we read two characters
      i++;
    } else {
      tmpDecoded.append(1, c);
    }
  }
  Ref<String> decoded(new String(tmpDecoded));
  return decoded;
}
} // namespace oned
} // namespace zxing

// file: zxing/oned/Code93Reader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include "Code93Reader.h"
// #include <zxing/oned/OneDResultPoint.h>
// #include <zxing/common/Array.h>
// #include <zxing/ReaderException.h>
// #include <zxing/FormatException.h>
// #include <zxing/NotFoundException.h>
// #include <zxing/ChecksumException.h>
// #include <math.h>
// #include <limits.h>

namespace zxing {
namespace oned {
namespace code93 {
        
  char const ALPHABET[] =
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ-. $/+%abcd*";
  string ALPHABET_STRING (ALPHABET);

  /**
   * These represent the encodings of characters, as patterns of wide and narrow bars.
   * The 9 least-significant bits of each int correspond to the pattern of wide and narrow.
   */
  int const CHARACTER_ENCODINGS[] = {
    0x114, 0x148, 0x144, 0x142, 0x128, 0x124, 0x122, 0x150, 0x112, 0x10A, // 0-9
    0x1A8, 0x1A4, 0x1A2, 0x194, 0x192, 0x18A, 0x168, 0x164, 0x162, 0x134, // A-J
    0x11A, 0x158, 0x14C, 0x146, 0x12C, 0x116, 0x1B4, 0x1B2, 0x1AC, 0x1A6, // K-T
    0x196, 0x19A, 0x16C, 0x166, 0x136, 0x13A, // U-Z
    0x12E, 0x1D4, 0x1D2, 0x1CA, 0x16E, 0x176, 0x1AE, // - - %
    0x126, 0x1DA, 0x1D6, 0x132, 0x15E, // Control chars? $-*
  };
  int const CHARACTER_ENCODINGS_LENGTH =
    (int)sizeof(CHARACTER_ENCODINGS)/sizeof(CHARACTER_ENCODINGS[0]);
  const int ASTERISK_ENCODING = CHARACTER_ENCODINGS[47];
}

Code93Reader::Code93Reader() {
  decodeRowResult.reserve(20);
  counters.resize(6);
}

Ref<Result> Code93Reader::decodeRow(int rowNumber, Ref<BitArray> row) {
  Range start (findAsteriskPattern(row));
  // Read off white space
  int nextStart = row->getNextSet(start[1]);
  int end = row->getSize();

  vector<int>& theCounters (counters);
  { // Arrays.fill(counters, 0);
    unsigned long size = theCounters.size();
    theCounters.resize(0);
    theCounters.resize(size); }
  string& result (decodeRowResult);
  result.clear();

  char decodedChar;
  int lastStart;
  do {
    recordPattern(row, nextStart, theCounters);
    int pattern = toPattern(theCounters);
    if (pattern < 0) {
      throw NotFoundException();
    }
    decodedChar = patternToChar(pattern);
    result.append(1, decodedChar);
    lastStart = nextStart;
    for(unsigned long i=0, e=theCounters.size(); i < e; ++i) {
      nextStart += theCounters[i];
    }
    // Read off white space
    nextStart = row->getNextSet(nextStart);
  } while (decodedChar != '*');
  result.resize(result.length() - 1); // remove asterisk

  // Look for whitespace after pattern:
  int lastPatternSize = 0;
  for (unsigned long i = 0, e = theCounters.size(); i < e; i++) {
    lastPatternSize += theCounters[i];
  }

  // Should be at least one more black module
  if (nextStart == end || !row->get(nextStart)) {
    throw NotFoundException();
  }

  if (result.length() < 2) {
    // false positive -- need at least 2 checksum digits
    throw NotFoundException();
  }

  checkChecksums(result);
  // Remove checksum digits
  result.resize(result.length() - 2);

  Ref<String> resultString = decodeExtended(result);

  float left = (float) (start[1] + start[0]) / 2.0f;
  float right = lastStart + lastPatternSize / 2.0f;

  ArrayRef< Ref<ResultPoint> > resultPoints (2);
  resultPoints[0] =
    Ref<OneDResultPoint>(new OneDResultPoint(left, (float) rowNumber));
  resultPoints[1] =
    Ref<OneDResultPoint>(new OneDResultPoint(right, (float) rowNumber));

  return Ref<Result>(new Result(
                       resultString,
                       ArrayRef<char>(),
                       resultPoints,
                       BarcodeFormat::CODE_93));
}

Code93Reader::Range Code93Reader::findAsteriskPattern(Ref<BitArray> row)  {
  int width = row->getSize();
  int rowOffset = row->getNextSet(0);

  { // Arrays.fill(counters, 0);
    unsigned long size = counters.size();
    counters.resize(0);
    counters.resize(size); }
  vector<int>& theCounters (counters);

  int patternStart = rowOffset;
  bool isWhite = false;
  unsigned long patternLength = theCounters.size();

  int counterPosition = 0;
  for (int i = rowOffset; i < width; i++) {
    if (row->get(i) ^ isWhite) {
      theCounters[counterPosition]++;
    } else {
      if (counterPosition == patternLength - 1) {
          if (toPattern(theCounters) == code93::ASTERISK_ENCODING) {
          return Range(patternStart, i);
        }
        patternStart += theCounters[0] + theCounters[1];
        for (int y = 2; y < patternLength; y++) {
          theCounters[y - 2] = theCounters[y];
        }
        theCounters[patternLength - 2] = 0;
        theCounters[patternLength - 1] = 0;
        counterPosition--;
      } else {
        counterPosition++;
      }
      theCounters[counterPosition] = 1;
      isWhite = !isWhite;
    }
  }
  throw NotFoundException();
}

int Code93Reader::toPattern(vector<int>& counters) {
  unsigned long max = counters.size();
  int sum = 0;
  for(unsigned long i=0, e=counters.size(); i<e; ++i) {
    sum += counters[i];
  }
  int pattern = 0;
  for (int i = 0; i < max; i++) {
    int scaledShifted = (counters[i] << INTEGER_MATH_SHIFT) * 9 / sum;
    int scaledUnshifted = scaledShifted >> INTEGER_MATH_SHIFT;
    if ((scaledShifted & 0xFF) > 0x7F) {
      scaledUnshifted++;
    }
    if (scaledUnshifted < 1 || scaledUnshifted > 4) {
      return -1;
    }
    if ((i & 0x01) == 0) {
      for (int j = 0; j < scaledUnshifted; j++) {
        pattern = (pattern << 1) | 0x01;
      }
    } else {
      pattern <<= scaledUnshifted;
    }
  }
  return pattern;
}

char Code93Reader::patternToChar(int pattern)  {
  for (int i = 0; i < code93::CHARACTER_ENCODINGS_LENGTH; i++) {
    if (code93::CHARACTER_ENCODINGS[i] == pattern) {
      return code93::ALPHABET[i];
    }
  }
  throw NotFoundException();
}

Ref<String> Code93Reader::decodeExtended(string const& encoded)  {
  unsigned long length = encoded.length();
  string decoded;
  for (int i = 0; i < length; i++) {
    char c = encoded[i];
    if (c >= 'a' && c <= 'd') {
      if (i >= length - 1) {
        throw FormatException::getFormatInstance();
      }
      char next = encoded[i + 1];
      char decodedChar = '\0';
      switch (c) {
      case 'd':
        // +A to +Z map to a to z
        if (next >= 'A' && next <= 'Z') {
          decodedChar = (char) (next + 32);
        } else {
          throw FormatException::getFormatInstance();
        }
        break;
      case 'a':
        // $A to $Z map to control codes SH to SB
        if (next >= 'A' && next <= 'Z') {
          decodedChar = (char) (next - 64);
        } else {
          throw FormatException::getFormatInstance();
        }
        break;
	  case 'b':
		if (next >= 'A' && next <= 'E') {
		  // %A to %E map to control codes ESC to USep
		  decodedChar = (char) (next - 38);
		} else if (next >= 'F' && next <= 'J') {
		  // %F to %J map to ; < = > ?
		  decodedChar = (char) (next - 11);
		} else if (next >= 'K' && next <= 'O') {
		  // %K to %O map to [ \ ] ^ _
		  decodedChar = (char) (next + 16);
		} else if (next >= 'P' && next <= 'S') {
		  // %P to %S map to { | } ~
		  decodedChar = (char) (next + 43);
		} else if (next >= 'T' && next <= 'Z') {
		  // %T to %Z all map to DEL (127)
		  decodedChar = 127;
		} else {
		  throw FormatException::getFormatInstance();
		}
		break;
      case 'c':
        // /A to /O map to ! to , and /Z maps to :
        if (next >= 'A' && next <= 'O') {
          decodedChar = (char) (next - 32);
        } else if (next == 'Z') {
          decodedChar = ':';
        } else {
          throw FormatException::getFormatInstance();
        }
        break;
      }
      decoded.append(1, decodedChar);
      // bump up i again since we read two characters
      i++;
    } else {
      decoded.append(1, c);
    }
  }
  return Ref<String>(new String(decoded));
}

void Code93Reader::checkChecksums(string const& result) {
  int length = (int)result.length();
  checkOneChecksum(result, length - 2, 20);
  checkOneChecksum(result, length - 1, 15);
}

void Code93Reader::checkOneChecksum(string const& result,
                                    int checkPosition,
                                    int weightMax) {
  int weight = 1;
  int total = 0;
  for (int i = checkPosition - 1; i >= 0; i--) {
    total += weight * code93::ALPHABET_STRING.find_first_of(result[i]);
    if (++weight > weightMax) {
      weight = 1;
    }
  }
  if (result[checkPosition] != code93::ALPHABET[total % 47]) {
    throw ChecksumException();
  }
}
}
}

// file: zxing/oned/EAN13Reader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include "EAN13Reader.h"
// #include <zxing/NotFoundException.h>

namespace zxing {
namespace oned {
        
namespace {
  const int FIRST_DIGIT_ENCODINGS[10] = {
    0x00, 0x0B, 0x0D, 0xE, 0x13, 0x19, 0x1C, 0x15, 0x16, 0x1A
  };
}

EAN13Reader::EAN13Reader() : decodeMiddleCounters(4, 0) { }

int EAN13Reader::decodeMiddle(Ref<BitArray> row,
                              Range const& startRange,
                              std::string& resultString) {
  vector<int>& counters (decodeMiddleCounters);
  counters.clear();
  counters.resize(4);
  int end = row->getSize();
  int rowOffset = startRange[1];

  int lgPatternFound = 0;

  for (int x = 0; x < 6 && rowOffset < end; x++) {
    int bestMatch = decodeDigit(row, counters, rowOffset, L_AND_G_PATTERNS);
    resultString.append(1, (char) ('0' + bestMatch % 10));
    for (unsigned long i = 0, end = counters.size(); i <end; i++) {
      rowOffset += counters[i];
    }
    if (bestMatch >= 10) {
      lgPatternFound |= 1 << (5 - x);
    }
  }

  determineFirstDigit(resultString, lgPatternFound);

  Range middleRange = findGuardPattern(row, rowOffset, true, MIDDLE_PATTERN) ;
  rowOffset = middleRange[1];

  for (int x = 0; x < 6 && rowOffset < end; x++) {
    int bestMatch =
      decodeDigit(row, counters, rowOffset, L_PATTERNS);
    resultString.append(1, (char) ('0' + bestMatch));
    for (unsigned long i = 0, end = counters.size(); i < end; i++) {
      rowOffset += counters[i];
    }
  }
  return rowOffset;
}

void EAN13Reader::determineFirstDigit(std::string& resultString, int lgPatternFound) {
  // std::cerr << "K " << resultString << " " << lgPatternFound << " " <<FIRST_DIGIT_ENCODINGS << std::endl;
  for (int d = 0; d < 10; d++) {
    if (lgPatternFound == FIRST_DIGIT_ENCODINGS[d]) {
      resultString.insert(0, 1, (char) ('0' + d));
      return;
    }
  }
  throw NotFoundException();
}

zxing::BarcodeFormat EAN13Reader::getBarcodeFormat(){
  return BarcodeFormat::EAN_13;
}
}
}

// file: zxing/oned/EAN8Reader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include "EAN8Reader.h"
// #include <zxing/ReaderException.h>

namespace zxing {
namespace oned {
        
EAN8Reader::EAN8Reader() : decodeMiddleCounters(4, 0) {}

int EAN8Reader::decodeMiddle(Ref<BitArray> row,
                             Range const& startRange,
                             std::string& result){
  vector<int>& counters (decodeMiddleCounters);
  counters[0] = 0;
  counters[1] = 0;
  counters[2] = 0;
  counters[3] = 0;

  int end = row->getSize();
  int rowOffset = startRange[1];

  for (int x = 0; x < 4 && rowOffset < end; x++) {
    int bestMatch = decodeDigit(row, counters, rowOffset, L_PATTERNS);
    result.append(1, (char) ('0' + bestMatch));
    for (unsigned long i = 0, end = counters.size(); i < end; i++) {
      rowOffset += counters[i];
    }
  }

  Range middleRange =
    findGuardPattern(row, rowOffset, true, MIDDLE_PATTERN);
  rowOffset = middleRange[1];
  for (int x = 0; x < 4 && rowOffset < end; x++) {
    int bestMatch = decodeDigit(row, counters, rowOffset, L_PATTERNS);
    result.append(1, (char) ('0' + bestMatch));
    for (unsigned long i = 0, end = counters.size(); i < end; i++) {
      rowOffset += counters[i];
    }
  }
  return rowOffset;
}

zxing::BarcodeFormat EAN8Reader::getBarcodeFormat(){
  return BarcodeFormat::EAN_8;
}
}
}

// file: zxing/oned/ITFReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/ZXing.h>
// #include <zxing/oned/ITFReader.h>
// #include <zxing/oned/OneDResultPoint.h>
// #include <zxing/common/Array.h>
// #include <zxing/ReaderException.h>
// #include <zxing/FormatException.h>
// #include <zxing/NotFoundException.h>
// #include <math.h>

namespace zxing {
namespace oned {
        
#define VECTOR_INIT(v) v, v + sizeof(v)/sizeof(v[0])

namespace {

const int W = 3; // Pixel width of a wide line
const int N = 1; // Pixed width of a narrow line

const int DEFAULT_ALLOWED_LENGTHS_[] =
{ 48, 44, 24, 20, 18, 16, 14, 12, 10, 8, 6 };
const ArrayRef<int> DEFAULT_ALLOWED_LENGTHS (new Array<int>(VECTOR_INIT(DEFAULT_ALLOWED_LENGTHS_)));

/**
 * Start/end guard pattern.
 *
 * Note: The end pattern is reversed because the row is reversed before
 * searching for the END_PATTERN
 */
const int START_PATTERN_[] = {N, N, N, N};
const vector<int> START_PATTERN (VECTOR_INIT(START_PATTERN_));

const int END_PATTERN_REVERSED_[] = {N, N, W};
const vector<int> END_PATTERN_REVERSED (VECTOR_INIT(END_PATTERN_REVERSED_));

/**
 * Patterns of Wide / Narrow lines to indicate each digit
 */
const int PATTERNS[][5] = {
  {N, N, W, W, N}, // 0
  {W, N, N, N, W}, // 1
  {N, W, N, N, W}, // 2
  {W, W, N, N, N}, // 3
  {N, N, W, N, W}, // 4
  {W, N, W, N, N}, // 5
  {N, W, W, N, N}, // 6
  {N, N, N, W, W}, // 7
  {W, N, N, W, N}, // 8
  {N, W, N, W, N}  // 9
};

}

ITFReader::ITFReader() : narrowLineWidth(-1) {
}


Ref<Result> ITFReader::decodeRow(int rowNumber, Ref<BitArray> row) {
  // Find out where the Middle section (payload) starts & ends

  Range startRange = decodeStart(row);
  Range endRange = decodeEnd(row);

  std::string result;
  decodeMiddle(row, startRange[1], endRange[0], result);
  Ref<String> resultString(new String(result));

  ArrayRef<int> allowedLengths;
  // Java hints stuff missing
  if (!allowedLengths) {
    allowedLengths = DEFAULT_ALLOWED_LENGTHS;
  }

  // To avoid false positives with 2D barcodes (and other patterns), make
  // an assumption that the decoded string must be 6, 10 or 14 digits.
  int length = resultString->size();
  bool lengthOK = false;
  for (int i = 0, e = (int)allowedLengths->size(); i < e; i++) {
    if (length == allowedLengths[i]) {
      lengthOK = true;
      break;
    }
  }

  if (!lengthOK) {
    throw FormatException();
  }

  ArrayRef< Ref<ResultPoint> > resultPoints(2);
  resultPoints[0] =
      Ref<OneDResultPoint>(new OneDResultPoint(float(startRange[1]), float(rowNumber)));
  resultPoints[1] =
      Ref<OneDResultPoint>(new OneDResultPoint(float(endRange[0]), float(rowNumber)));
  return Ref<Result>(new Result(resultString, ArrayRef<char>(), resultPoints, BarcodeFormat::ITF));
}

/**
 * @param row          row of black/white values to search
 * @param payloadStart offset of start pattern
 * @param resultString {@link StringBuffer} to append decoded chars to
 * @throws ReaderException if decoding could not complete successfully
 */
void ITFReader::decodeMiddle(Ref<BitArray> row,
                             int payloadStart,
                             int payloadEnd,
                             std::string& resultString) {
  // Digits are interleaved in pairs - 5 black lines for one digit, and the
  // 5
  // interleaved white lines for the second digit.
  // Therefore, need to scan 10 lines and then
  // split these into two arrays
  vector<int> counterDigitPair(10, 0);
  vector<int> counterBlack(5, 0);
  vector<int> counterWhite(5, 0);

  while (payloadStart < payloadEnd) {

    // Get 10 runs of black/white.
    recordPattern(row, payloadStart, counterDigitPair);
    // Split them into each array
    for (int k = 0; k < 5; k++) {
      int twoK = k << 1;
      counterBlack[k] = counterDigitPair[twoK];
      counterWhite[k] = counterDigitPair[twoK + 1];
    }

    int bestMatch = decodeDigit(counterBlack);
    resultString.append(1, (char) ('0' + bestMatch));
    bestMatch = decodeDigit(counterWhite);
    resultString.append(1, (char) ('0' + bestMatch));

    for (unsigned long i = 0, e = counterDigitPair.size(); i < e; i++) {
      payloadStart += counterDigitPair[i];
    }
  }
}

/**
 * Identify where the start of the middle / payload section starts.
 *
 * @param row row of black/white values to search
 * @return Array, containing index of start of 'start block' and end of
 *         'start block'
 * @throws ReaderException
 */
ITFReader::Range ITFReader::decodeStart(Ref<BitArray> row) {
  int endStart = skipWhiteSpace(row);
  Range startPattern = findGuardPattern(row, endStart, START_PATTERN);

  // Determine the width of a narrow line in pixels. We can do this by
  // getting the width of the start pattern and dividing by 4 because its
  // made up of 4 narrow lines.
  narrowLineWidth = (startPattern[1] - startPattern[0]) >> 2;

  validateQuietZone(row, startPattern[0]);
  return startPattern;
}

/**
 * Identify where the end of the middle / payload section ends.
 *
 * @param row row of black/white values to search
 * @return Array, containing index of start of 'end block' and end of 'end
 *         block'
 * @throws ReaderException
 */

ITFReader::Range ITFReader::decodeEnd(Ref<BitArray> row) {
  // For convenience, reverse the row and then
  // search from 'the start' for the end block
  BitArray::Reverse r (row);

  int endStart = skipWhiteSpace(row);
  Range endPattern = findGuardPattern(row, endStart, END_PATTERN_REVERSED);

  // The start & end patterns must be pre/post fixed by a quiet zone. This
  // zone must be at least 10 times the width of a narrow line.
  // ref: http://www.barcode-1.net/i25code.html
  validateQuietZone(row, endPattern[0]);

  // Now recalculate the indices of where the 'endblock' starts & stops to
  // accommodate
  // the reversed nature of the search
  int temp = endPattern[0];
  endPattern[0] = row->getSize() - endPattern[1];
  endPattern[1] = row->getSize() - temp;

  return endPattern;
}

/**
 * The start & end patterns must be pre/post fixed by a quiet zone. This
 * zone must be at least 10 times the width of a narrow line.  Scan back until
 * we either get to the start of the barcode or match the necessary number of
 * quiet zone pixels.
 *
 * Note: Its assumed the row is reversed when using this method to find
 * quiet zone after the end pattern.
 *
 * ref: http://www.barcode-1.net/i25code.html
 *
 * @param row bit array representing the scanned barcode.
 * @param startPattern index into row of the start or end pattern.
 * @throws ReaderException if the quiet zone cannot be found, a ReaderException is thrown.
 */
void ITFReader::validateQuietZone(Ref<BitArray> row, int startPattern) {
  int quietCount = this->narrowLineWidth * 10;  // expect to find this many pixels of quiet zone

  for (int i = startPattern - 1; quietCount > 0 && i >= 0; i--) {
    if (row->get(i)) {
      break;
    }
    quietCount--;
  }
  if (quietCount != 0) {
    // Unable to find the necessary number of quiet zone pixels.
    throw NotFoundException();
  }
}

/**
 * Skip all whitespace until we get to the first black line.
 *
 * @param row row of black/white values to search
 * @return index of the first black line.
 * @throws ReaderException Throws exception if no black lines are found in the row
 */
int ITFReader::skipWhiteSpace(Ref<BitArray> row) {
  int width = row->getSize();
  int endStart = row->getNextSet(0);
  if (endStart == width) {
    throw NotFoundException();
  }
  return endStart;
}

/**
 * @param row       row of black/white values to search
 * @param rowOffset position to start search
 * @param pattern   pattern of counts of number of black and white pixels that are
 *                  being searched for as a pattern
 * @return start/end horizontal offset of guard pattern, as an array of two
 *         ints
 * @throws ReaderException if pattern is not found
 */
ITFReader::Range ITFReader::findGuardPattern(Ref<BitArray> row,
                                             int rowOffset,
                                             vector<int> const& pattern) {
  // TODO: This is very similar to implementation in UPCEANReader. Consider if they can be
  // merged to a single method.
  unsigned long patternLength = pattern.size();
  vector<int> counters(patternLength);
  int width = row->getSize();
  bool isWhite = false;

  int counterPosition = 0;
  int patternStart = rowOffset;
  for (int x = rowOffset; x < width; x++) {
    if (row->get(x) ^ isWhite) {
      counters[counterPosition]++;
    } else {
      if (counterPosition == patternLength - 1) {
        if (patternMatchVariance(counters, &pattern[0], MAX_INDIVIDUAL_VARIANCE) < MAX_AVG_VARIANCE) {
          return Range(patternStart, x);
        }
        patternStart += counters[0] + counters[1];
        for (int y = 2; y < patternLength; y++) {
          counters[y - 2] = counters[y];
        }
        counters[patternLength - 2] = 0;
        counters[patternLength - 1] = 0;
        counterPosition--;
      } else {
        counterPosition++;
      }
      counters[counterPosition] = 1;
      isWhite = !isWhite;
    }
  }
  throw NotFoundException();
}

/**
 * Attempts to decode a sequence of ITF black/white lines into single
 * digit.
 *
 * @param counters the counts of runs of observed black/white/black/... values
 * @return The decoded digit
 * @throws ReaderException if digit cannot be decoded
 */
int ITFReader::decodeDigit(vector<int>& counters){

  int bestVariance = MAX_AVG_VARIANCE; // worst variance we'll accept
  int bestMatch = -1;
  int max = sizeof(PATTERNS)/sizeof(PATTERNS[0]);
  for (int i = 0; i < max; i++) {
    int const* pattern = PATTERNS[i];
    int variance = patternMatchVariance(counters, pattern, MAX_INDIVIDUAL_VARIANCE);
    if (variance < bestVariance) {
      bestVariance = variance;
      bestMatch = i;
    }
  }
  if (bestMatch >= 0) {
    return bestMatch;
  } else {
    throw NotFoundException();
  }
}

ITFReader::~ITFReader(){}
}
}

// file: zxing/oned/MultiFormatOneDReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/ZXing.h>
// #include <zxing/oned/MultiFormatOneDReader.h>
// #include <zxing/oned/MultiFormatUPCEANReader.h>
// #include <zxing/oned/Code39Reader.h>
// #include <zxing/oned/Code128Reader.h>
// #include <zxing/oned/Code93Reader.h>
// #include <zxing/oned/CodaBarReader.h>
// #include <zxing/oned/ITFReader.h>
// #include <zxing/ReaderException.h>
// #include <zxing/NotFoundException.h>

namespace zxing {
namespace oned {
        
MultiFormatOneDReader::MultiFormatOneDReader(DecodeHints hints) : readers() {
  if (hints.containsFormat(BarcodeFormat::EAN_13) ||
      hints.containsFormat(BarcodeFormat::EAN_8) ||
      hints.containsFormat(BarcodeFormat::UPC_A) ||
      hints.containsFormat(BarcodeFormat::UPC_E)) {
    readers.push_back(Ref<OneDReader>(new MultiFormatUPCEANReader(hints)));
  }
  if (hints.containsFormat(BarcodeFormat::CODE_39)) {
    readers.push_back(Ref<OneDReader>(new Code39Reader()));
  }
  if (hints.containsFormat(BarcodeFormat::CODE_93)) {
    readers.push_back(Ref<OneDReader>(new Code93Reader()));
  }
  if (hints.containsFormat(BarcodeFormat::CODE_128)) {
    readers.push_back(Ref<OneDReader>(new Code128Reader()));
  }
  if (hints.containsFormat(BarcodeFormat::ITF)) {
    readers.push_back(Ref<OneDReader>(new ITFReader()));
  }
  if (hints.containsFormat(BarcodeFormat::CODABAR)) {
    readers.push_back(Ref<OneDReader>(new CodaBarReader()));
  }
/*
  if (hints.containsFormat(BarcodeFormat::RSS_14)) {
    readers.push_back(Ref<OneDReader>(new RSS14Reader()));
  }
*/
/*
  if (hints.containsFormat(BarcodeFormat::RSS_EXPANDED)) {
    readers.push_back(Ref<OneDReader>(new RSS14ExpandedReader()));
  }
*/
  if (readers.size() == 0) {
    readers.push_back(Ref<OneDReader>(new MultiFormatUPCEANReader(hints)));
    readers.push_back(Ref<OneDReader>(new Code39Reader()));
    readers.push_back(Ref<OneDReader>(new CodaBarReader()));
    readers.push_back(Ref<OneDReader>(new Code93Reader()));
    readers.push_back(Ref<OneDReader>(new Code128Reader()));
    readers.push_back(Ref<OneDReader>(new ITFReader()));
    // readers.push_back(Ref<OneDReader>(new RSS14Reader()));
    // readers.push_back(Ref<OneDReader>(new RSS14ExpandedReader()));
  }
}

// #include <typeinfo>

Ref<Result> MultiFormatOneDReader::decodeRow(int rowNumber, Ref<BitArray> row) {
  unsigned long size = readers.size();
  for (unsigned long i = 0; i < size; i++) {
    OneDReader* reader = readers[i];
    try {
      Ref<Result> result = reader->decodeRow(rowNumber, row);
      return result;
    } catch (ReaderException const& re) {
      (void)re;
      // continue
    }
  }
  throw NotFoundException();
}
}
}

// file: zxing/oned/MultiFormatUPCEANReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  MultiFormatUPCEANReader.cpp
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

// #include <zxing/ZXing.h>
// #include <zxing/oned/MultiFormatUPCEANReader.h>
// #include <zxing/oned/EAN13Reader.h>
// #include <zxing/oned/EAN8Reader.h>
// #include <zxing/oned/UPCEReader.h>
// #include <zxing/oned/UPCAReader.h>
// #include <zxing/oned/OneDResultPoint.h>
// #include <zxing/common/Array.h>
// #include <zxing/ReaderException.h>
// #include <zxing/NotFoundException.h>
// #include <math.h>

namespace zxing {
namespace oned {
        
MultiFormatUPCEANReader::MultiFormatUPCEANReader(DecodeHints hints) : readers() {
  if (hints.containsFormat(BarcodeFormat::EAN_13)) {
    readers.push_back(Ref<UPCEANReader>(new EAN13Reader()));
  } else if (hints.containsFormat(BarcodeFormat::UPC_A)) {
    readers.push_back(Ref<UPCEANReader>(new UPCAReader()));
  }
  if (hints.containsFormat(BarcodeFormat::EAN_8)) {
    readers.push_back(Ref<UPCEANReader>(new EAN8Reader()));
  }
  if (hints.containsFormat(BarcodeFormat::UPC_E)) {
    readers.push_back(Ref<UPCEANReader>(new UPCEReader()));
  }
  if (readers.size() == 0) {
    readers.push_back(Ref<UPCEANReader>(new EAN13Reader()));
    // UPC-A is covered by EAN-13
    readers.push_back(Ref<UPCEANReader>(new EAN8Reader()));
    readers.push_back(Ref<UPCEANReader>(new UPCEReader()));
  }
}

// #include <typeinfo>

Ref<Result> MultiFormatUPCEANReader::decodeRow(int rowNumber, Ref<BitArray> row) {
  // Compute this location once and reuse it on multiple implementations
  UPCEANReader::Range startGuardPattern = UPCEANReader::findStartGuardPattern(row);
  for (unsigned long i = 0, e = readers.size(); i < e; i++) {
    Ref<UPCEANReader> reader = readers[i];
    Ref<Result> result;
    try {
      result = reader->decodeRow(rowNumber, row, startGuardPattern);
    } catch (ReaderException const& ignored) {
      (void)ignored;
      continue;
    }

    // Special case: a 12-digit code encoded in UPC-A is identical
    // to a "0" followed by those 12 digits encoded as EAN-13. Each
    // will recognize such a code, UPC-A as a 12-digit string and
    // EAN-13 as a 13-digit string starting with "0".  Individually
    // these are correct and their readers will both read such a
    // code and correctly call it EAN-13, or UPC-A, respectively.
    //
    // In this case, if we've been looking for both types, we'd like
    // to call it a UPC-A code. But for efficiency we only run the
    // EAN-13 decoder to also read UPC-A. So we special case it
    // here, and convert an EAN-13 result to a UPC-A result if
    // appropriate.
    bool ean13MayBeUPCA =
      result->getBarcodeFormat() == BarcodeFormat::EAN_13 &&
      result->getText()->charAt(0) == '0';

    // Note: doesn't match Java which uses hints

    bool canReturnUPCA = true;

    if (ean13MayBeUPCA && canReturnUPCA) {
      // Transfer the metdata across
      Ref<Result> resultUPCA (new Result(result->getText()->substring(1),
                                         result->getRawBytes(),
                                         result->getResultPoints(),
                                         BarcodeFormat::UPC_A));
      // needs java metadata stuff
      return resultUPCA;
    }
    return result;
  }

  throw NotFoundException();
}
}
}

// file: zxing/oned/OneDReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/ZXing.h>
// #include <zxing/oned/OneDReader.h>
// #include <zxing/ReaderException.h>
// #include <zxing/oned/OneDResultPoint.h>
// #include <zxing/NotFoundException.h>
// #include <math.h>
// #include <limits.h>
// #include <algorithm>  // vs12, std::min und std:max

namespace zxing {
namespace oned {
using namespace std;

OneDReader::OneDReader() {}

Ref<Result> OneDReader::decode(Ref<BinaryBitmap> image, DecodeHints hints) {
  try {
    return doDecode(image, hints);
  } catch (NotFoundException const& nfe) {
    // std::cerr << "trying harder" << std::endl;
//    bool tryHarder = hints.getTryHarder();
//    if (tryHarder && image->isRotateSupported()) {
      // std::cerr << "v rotate" << std::endl;
      Ref<BinaryBitmap> rotatedImage(image->rotateCounterClockwise());
      // std::cerr << "^ rotate" << std::endl;
      Ref<Result> result = doDecode(rotatedImage, hints);
      // Doesn't have java metadata stuff
      ArrayRef< Ref<ResultPoint> >& points (result->getResultPoints());
      if (points && !points->empty()) {
        int height = rotatedImage->getHeight();
        for (int i = 0; i < points->size(); i++) {
          points[i].reset(new OneDResultPoint(height - points[i]->getY() - 1, points[i]->getX()));
        }
//      }
      // std::cerr << "tried harder" << std::endl;
      return result;
    } else {
      // std::cerr << "tried harder nfe" << std::endl;
      throw nfe;
    }
  }
}

// #include <typeinfo>

Ref<Result> OneDReader::doDecode(Ref<BinaryBitmap> image, DecodeHints hints) {
  int width = image->getWidth();
  int height = image->getHeight();
  Ref<BitArray> row(new BitArray(width));

  int middle = height >> 1;
  bool tryHarder = hints.getTryHarder();
  int rowStep = std::max(1, height >> (tryHarder ? 8 : 5));
  using namespace std;
  // cerr << "rS " << rowStep << " " << height << " " << tryHarder << endl;
  int maxLines;
  if (tryHarder) {
    maxLines = height; // Look at the whole image, not just the center
  } else {
    maxLines = 15; // 15 rows spaced 1/32 apart is roughly the middle half of the image
  }

  for (int x = 0; x < maxLines; x++) {

    // Scanning from the middle out. Determine which row we're looking at next:
    int rowStepsAboveOrBelow = (x + 1) >> 1;
    bool isAbove = (x & 0x01) == 0; // i.e. is x even?
    int rowNumber = middle + rowStep * (isAbove ? rowStepsAboveOrBelow : -rowStepsAboveOrBelow);
    if (false) {
      std::cerr << "rN "
                << rowNumber << " "
                << height << " "
                << middle << " "
                << rowStep << " "
                << isAbove << " "
                << rowStepsAboveOrBelow
                << std::endl;
    }
    if (rowNumber < 0 || rowNumber >= height) {
      // Oops, if we run off the top or bottom, stop
      break;
    }

    // Estimate black point for this row and load it:
    try {
      row = image->getBlackRow(rowNumber, row);
    } catch (NotFoundException const& ignored) {
      (void)ignored;
      continue;
    }

    // While we have the image data in a BitArray, it's fairly cheap to reverse it in place to
    // handle decoding upside down barcodes.
    for (int attempt = 0; attempt < 2; attempt++) {
      if (attempt == 1) {
        row->reverse(); // reverse the row and continue
      }

      // Java hints stuff missing

      try {
        // Look for a barcode
        // std::cerr << "rn " << rowNumber << " " << typeid(*this).name() << std::endl;
        Ref<Result> result = decodeRow(rowNumber, row);
        // We found our barcode
        if (attempt == 1) {
          // But it was upside down, so note that
          // result.putMetadata(ResultMetadataType.ORIENTATION, new Integer(180));
          // And remember to flip the result points horizontally.
          ArrayRef< Ref<ResultPoint> > points(result->getResultPoints());
          if (points) {
            points[0] = Ref<ResultPoint>(new OneDResultPoint(width - points[0]->getX() - 1,
                                                             points[0]->getY()));
            points[1] = Ref<ResultPoint>(new OneDResultPoint(width - points[1]->getX() - 1,
                                                             points[1]->getY()));

          }
        }
        return result;
      } catch (ReaderException const& re) {
        (void)re;
        continue;
      }
    }
  }
  throw NotFoundException();
}

int OneDReader::patternMatchVariance(vector<int>& counters,
                                     vector<int> const& pattern,
                                     int maxIndividualVariance) {
  return patternMatchVariance(counters, &pattern[0], maxIndividualVariance);
}

int OneDReader::patternMatchVariance(vector<int>& counters,
                                     int const pattern[],
                                     int maxIndividualVariance) {
  unsigned long numCounters = counters.size();
  unsigned int total = 0;
  unsigned int patternLength = 0;
  for (unsigned long i = 0; i < numCounters; i++) {
    total += counters[i];
    patternLength += pattern[i];
  }
  if (total < patternLength) {
    // If we don't even have one pixel per unit of bar width, assume this is too small
    // to reliably match, so fail:
    return INT_MAX;
  }
  // We're going to fake floating-point math in integers. We just need to use more bits.
  // Scale up patternLength so that intermediate values below like scaledCounter will have
  // more "significant digits"
  int unitBarWidth = (total << INTEGER_MATH_SHIFT) / patternLength;
  maxIndividualVariance = (maxIndividualVariance * unitBarWidth) >> INTEGER_MATH_SHIFT;

  int totalVariance = 0;
  for (int x = 0; x < numCounters; x++) {
    int counter = counters[x] << INTEGER_MATH_SHIFT;
    int scaledPattern = pattern[x] * unitBarWidth;
    int variance = counter > scaledPattern ? counter - scaledPattern : scaledPattern - counter;
    if (variance > maxIndividualVariance) {
      return INT_MAX;
    }
    totalVariance += variance;
  }
  return totalVariance / total;
}

void OneDReader::recordPattern(Ref<BitArray> row,
                               int start,
                               vector<int>& counters) {
  unsigned long numCounters = counters.size();
  for (unsigned long i = 0; i < numCounters; i++) {
    counters[i] = 0;
  }
  int end = row->getSize();
  if (start >= end) {
    throw NotFoundException();
  }
  bool isWhite = !row->get(start);
  int counterPosition = 0;
  int i = start;
  while (i < end) {
    if (row->get(i) ^ isWhite) { // that is, exactly one is true
      counters[counterPosition]++;
    } else {
      counterPosition++;
      if (counterPosition == numCounters) {
        break;
      } else {
        counters[counterPosition] = 1;
        isWhite = !isWhite;
      }
    }
    i++;
  }
  // If we read fully the last section of pixels and filled up our counters -- or filled
  // the last counter but ran off the side of the image, OK. Otherwise, a problem.
  if (!(counterPosition == numCounters || (counterPosition == numCounters - 1 && i == end))) {
    throw NotFoundException();
  }
}

OneDReader::~OneDReader() {}
}
}

// file: zxing/oned/OneDResultPoint.cpp

/*
 *  OneDResultPoint.cpp
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

// #include "OneDResultPoint.h"

namespace zxing {
	namespace oned {

		OneDResultPoint::OneDResultPoint(float posX, float posY) : ResultPoint(posX,posY) {
		}
	}
}

// file: zxing/oned/UPCAReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  UPCAReader.cpp
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

// #include "UPCAReader.h"
// #include <zxing/FormatException.h>

namespace zxing {
    namespace oned {
UPCAReader::UPCAReader() : ean13Reader() {}

Ref<Result> UPCAReader::decodeRow(int rowNumber, Ref<BitArray> row) {
  return maybeReturnResult(ean13Reader.decodeRow(rowNumber, row));
}

Ref<Result> UPCAReader::decodeRow(int rowNumber,
                                  Ref<BitArray> row,
                                  Range const& startGuardRange) {
  return maybeReturnResult(ean13Reader.decodeRow(rowNumber, row, startGuardRange));
}

Ref<Result> UPCAReader::decode(Ref<BinaryBitmap> image, DecodeHints hints) {
  return maybeReturnResult(ean13Reader.decode(image, hints));
}

int UPCAReader::decodeMiddle(Ref<BitArray> row,
                             Range const& startRange,
                             std::string& resultString) {
  return ean13Reader.decodeMiddle(row, startRange, resultString);
}

Ref<Result> UPCAReader::maybeReturnResult(Ref<Result> result) {
  const std::string& text = (result->getText())->getText();
  if (text[0] == '0') {
    Ref<String> resultString(new String(text.substr(1)));
    Ref<Result> res(new Result(resultString, result->getRawBytes(), result->getResultPoints(),
                               BarcodeFormat::UPC_A));
    return res;
  } else {
    throw FormatException();
  }
}

zxing::BarcodeFormat UPCAReader::getBarcodeFormat(){
  return BarcodeFormat::UPC_A;
}
}
}

// file: zxing/oned/UPCEANReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  UPCEANReader.cpp
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

// #include <zxing/ZXing.h>
// #include <zxing/oned/UPCEANReader.h>
// #include <zxing/oned/OneDResultPoint.h>
// #include <zxing/ReaderException.h>
// #include <zxing/NotFoundException.h>
// #include <zxing/FormatException.h>
// #include <zxing/ChecksumException.h>

#define LEN(v) ((int)(sizeof(v)/sizeof(v[0])))

namespace zxing {
namespace oned {

  /**
   * Start/end guard pattern.
   */
  const int START_END_PATTERN_[] = {1, 1, 1};
//  const int START_END_PATTERN_LEN = LEN(START_END_PATTERN_);

  /**
   * Pattern marking the middle of a UPC/EAN pattern, separating the two halves.
   */
  const int MIDDLE_PATTERN_[] = {1, 1, 1, 1, 1};
//  const int MIDDLE_PATTERN_LEN = LEN(MIDDLE_PATTERN_);

  /**
   * "Odd", or "L" patterns used to encode UPC/EAN digits.
   */
  const int L_PATTERNS_[][4] = {
    {3, 2, 1, 1}, // 0
    {2, 2, 2, 1}, // 1
    {2, 1, 2, 2}, // 2
    {1, 4, 1, 1}, // 3
    {1, 1, 3, 2}, // 4
    {1, 2, 3, 1}, // 5
    {1, 1, 1, 4}, // 6
    {1, 3, 1, 2}, // 7
    {1, 2, 1, 3}, // 8
    {3, 1, 1, 2}  // 9
  };
//  const int L_PATTERNS_LEN = LEN(L_PATTERNS_);

  /**
   * As above but also including the "even", or "G" patterns used to encode UPC/EAN digits.
   */
  const int L_AND_G_PATTERNS_[][4] = {
    {3, 2, 1, 1}, // 0
    {2, 2, 2, 1}, // 1
    {2, 1, 2, 2}, // 2
    {1, 4, 1, 1}, // 3
    {1, 1, 3, 2}, // 4
    {1, 2, 3, 1}, // 5
    {1, 1, 1, 4}, // 6
    {1, 3, 1, 2}, // 7
    {1, 2, 1, 3}, // 8
    {3, 1, 1, 2}, // 9
    {1, 1, 2, 3}, // 10 reversed 0
    {1, 2, 2, 2}, // 11 reversed 1
    {2, 2, 1, 2}, // 12 reversed 2
    {1, 1, 4, 1}, // 13 reversed 3
    {2, 3, 1, 1}, // 14 reversed 4
    {1, 3, 2, 1}, // 15 reversed 5
    {4, 1, 1, 1}, // 16 reversed 6
    {2, 1, 3, 1}, // 17 reversed 7
    {3, 1, 2, 1}, // 18 reversed 8
    {2, 1, 1, 3}  // 19 reversed 9
  };
//  const int L_AND_G_PATTERNS_LEN = LEN(L_AND_G_PATTERNS_);


const int UPCEANReader::MAX_AVG_VARIANCE = (int)(PATTERN_MATCH_RESULT_SCALE_FACTOR * 0.48f);
const int UPCEANReader::MAX_INDIVIDUAL_VARIANCE = (int)(PATTERN_MATCH_RESULT_SCALE_FACTOR * 0.7f);

#define VECTOR_INIT(v) v, v + sizeof(v)/sizeof(v[0])

const vector<int>
UPCEANReader::START_END_PATTERN (VECTOR_INIT(START_END_PATTERN_));

const vector<int>
UPCEANReader::MIDDLE_PATTERN (VECTOR_INIT(MIDDLE_PATTERN_));
const vector<int const*>
UPCEANReader::L_PATTERNS (VECTOR_INIT(L_PATTERNS_));
const vector<int const*>
UPCEANReader::L_AND_G_PATTERNS (VECTOR_INIT(L_AND_G_PATTERNS_));

UPCEANReader::UPCEANReader() {}

Ref<Result> UPCEANReader::decodeRow(int rowNumber, Ref<BitArray> row) {
  return decodeRow(rowNumber, row, findStartGuardPattern(row));
}

Ref<Result> UPCEANReader::decodeRow(int rowNumber,
                                    Ref<BitArray> row,
                                    Range const& startGuardRange) {
  string& result = decodeRowStringBuffer;
  result.clear();
  int endStart = decodeMiddle(row, startGuardRange, result);

  Range endRange = decodeEnd(row, endStart);

  // Make sure there is a quiet zone at least as big as the end pattern after the barcode.
  // The spec might want more whitespace, but in practice this is the maximum we can count on.

  int end = endRange[1];
  int quietEnd = end + (end - endRange[0]);
  if (quietEnd >= row->getSize() || !row->isRange(end, quietEnd, false)) {
    throw NotFoundException();
  }

  // UPC/EAN should never be less than 8 chars anyway
  if (result.length() < 8) {
    throw FormatException();
  }

  Ref<String> resultString (new String(result));
  if (!checkChecksum(resultString)) {
    throw ChecksumException();
  }

  float left = (float) (startGuardRange[1] + startGuardRange[0]) / 2.0f;
  float right = (float) (endRange[1] + endRange[0]) / 2.0f;
  BarcodeFormat format = getBarcodeFormat();
  ArrayRef< Ref<ResultPoint> > resultPoints(2);
  resultPoints[0] = Ref<ResultPoint>(new OneDResultPoint(left, (float) rowNumber));
  resultPoints[1] = Ref<ResultPoint>(new OneDResultPoint(right, (float) rowNumber));
  Ref<Result> decodeResult (new Result(resultString, ArrayRef<char>(), resultPoints, format));
  // Java extension and man stuff
  return decodeResult;
}

UPCEANReader::Range UPCEANReader::findStartGuardPattern(Ref<BitArray> row) {
  bool foundStart = false;
  Range startRange;
  int nextStart = 0;
  vector<int> counters(START_END_PATTERN.size(), 0);
  // std::cerr << "fsgp " << *row << std::endl;
  while (!foundStart) {
    for(int i=0; i < (int)START_END_PATTERN.size(); ++i) {
      counters[i] = 0;
    }
    startRange = findGuardPattern(row, nextStart, false, START_END_PATTERN, counters);
    // std::cerr << "sr " << startRange[0] << " " << startRange[1] << std::endl;
    int start = startRange[0];
    nextStart = startRange[1];
    // Make sure there is a quiet zone at least as big as the start pattern before the barcode.
    // If this check would run off the left edge of the image, do not accept this barcode,
    // as it is very likely to be a false positive.
    int quietStart = start - (nextStart - start);
    if (quietStart >= 0) {
      foundStart = row->isRange(quietStart, start, false);
    }
  }
  return startRange;
}

UPCEANReader::Range UPCEANReader::findGuardPattern(Ref<BitArray> row,
                                                   int rowOffset,
                                                   bool whiteFirst,
                                                   vector<int> const& pattern) {
  vector<int> counters (pattern.size(), 0);
  return findGuardPattern(row, rowOffset, whiteFirst, pattern, counters);
}

UPCEANReader::Range UPCEANReader::findGuardPattern(Ref<BitArray> row,
                                                   int rowOffset,
                                                   bool whiteFirst,
                                                   vector<int> const& pattern,
                                                   vector<int>& counters) {
  // cerr << "fGP " << rowOffset  << " " << whiteFirst << endl;
  if (false) {
    for(int i=0; i < (int)pattern.size(); ++i) {
      std::cerr << pattern[i];
    }
    std::cerr << std::endl;
  }
  unsigned long patternLength = pattern.size();
  int width = row->getSize();
  bool isWhite = whiteFirst;
  rowOffset = whiteFirst ? row->getNextUnset(rowOffset) : row->getNextSet(rowOffset);
  int counterPosition = 0;
  int patternStart = rowOffset;
  for (int x = rowOffset; x < width; x++) {
    // std::cerr << "rg " << x << " " << row->get(x) << std::endl;
    if (row->get(x) ^ isWhite) {
      counters[counterPosition]++;
    } else {
      if (counterPosition == patternLength - 1) {
        if (patternMatchVariance(counters, pattern, MAX_INDIVIDUAL_VARIANCE) < MAX_AVG_VARIANCE) {
          return Range(patternStart, x);
        }
        patternStart += counters[0] + counters[1];
        for (int y = 2; y < patternLength; y++) {
          counters[y - 2] = counters[y];
        }
        counters[patternLength - 2] = 0;
        counters[patternLength - 1] = 0;
        counterPosition--;
      } else {
        counterPosition++;
      }
      counters[counterPosition] = 1;
      isWhite = !isWhite;
    }
  }
  throw NotFoundException();
}

UPCEANReader::Range UPCEANReader::decodeEnd(Ref<BitArray> row, int endStart) {
  return findGuardPattern(row, endStart, false, START_END_PATTERN);
}

int UPCEANReader::decodeDigit(Ref<BitArray> row,
                              vector<int> & counters,
                              int rowOffset,
                              vector<int const*> const& patterns) {
  recordPattern(row, rowOffset, counters);
  int bestVariance = MAX_AVG_VARIANCE; // worst variance we'll accept
  int bestMatch = -1;
  unsigned long max = patterns.size();
  for (int i = 0; i < max; i++) {
    int const* pattern (patterns[i]);
    int variance = patternMatchVariance(counters, pattern, MAX_INDIVIDUAL_VARIANCE);
    if (variance < bestVariance) {
      bestVariance = variance;
      bestMatch = i;
    }
  }
  if (bestMatch >= 0) {
    return bestMatch;
  } else {
    throw NotFoundException();
  }
}

/**
 * @return {@link #checkStandardUPCEANChecksum(String)}
 */
bool UPCEANReader::checkChecksum(Ref<String> const& s) {
  return checkStandardUPCEANChecksum(s);
}

/**
 * Computes the UPC/EAN checksum on a string of digits, and reports
 * whether the checksum is correct or not.
 *
 * @param s string of digits to check
 * @return true iff string of digits passes the UPC/EAN checksum algorithm
 */
bool UPCEANReader::checkStandardUPCEANChecksum(Ref<String> const& s_) {
  std::string const& s (s_->getText());
  int length = (int)s.length();
  if (length == 0) {
    return false;
  }

  int sum = 0;
  for (int i = length - 2; i >= 0; i -= 2) {
    int digit = (int) s[i] - (int) '0';
    if (digit < 0 || digit > 9) {
      return false;
    }
    sum += digit;
  }
  sum *= 3;
  for (int i = length - 1; i >= 0; i -= 2) {
    int digit = (int) s[i] - (int) '0';
    if (digit < 0 || digit > 9) {
      return false;
    }
    sum += digit;
  }
  return sum % 10 == 0;
}

UPCEANReader::~UPCEANReader() {
}
}
}

// file: zxing/oned/UPCEReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/ZXing.h>
// #include <zxing/oned/UPCEReader.h>
// #include <zxing/ReaderException.h>

namespace zxing {
namespace oned {

#define VECTOR_INIT(v) v, v + sizeof(v)/sizeof(v[0])

namespace {
  /**
   * The pattern that marks the middle, and end, of a UPC-E pattern.
   * There is no "second half" to a UPC-E barcode.
   */
  const int MIDDLE_END_PATTERN_[6] = {1, 1, 1, 1, 1, 1};
  const vector<int> MIDDLE_END_PATTERN (VECTOR_INIT(MIDDLE_END_PATTERN_));


  /**
   * See {@link #L_AND_G_PATTERNS}; these values similarly represent patterns of
   * even-odd parity encodings of digits that imply both the number system (0 or 1)
   * used, and the check digit.
   */
  const int NUMSYS_AND_CHECK_DIGIT_PATTERNS[2][10] = {
    {0x38, 0x34, 0x32, 0x31, 0x2C, 0x26, 0x23, 0x2A, 0x29, 0x25},
    {0x07, 0x0B, 0x0D, 0x0E, 0x13, 0x19, 0x1C, 0x15, 0x16, 0x1A}
  };
}

UPCEReader::UPCEReader() {
}

int UPCEReader::decodeMiddle(Ref<BitArray> row, Range const& startRange, string& result) {
  vector<int>& counters (decodeMiddleCounters);
  counters.clear();
  counters.resize(4);
  int end = row->getSize();
  int rowOffset = startRange[1];

  int lgPatternFound = 0;

  for (int x = 0; x < 6 && rowOffset < end; x++) {
    int bestMatch = decodeDigit(row, counters, rowOffset, L_AND_G_PATTERNS);
    result.append(1, (char) ('0' + bestMatch % 10));
    for (unsigned long i = 0, e = counters.size(); i < e; i++) {
      rowOffset += counters[i];
    }
    if (bestMatch >= 10) {
      lgPatternFound |= 1 << (5 - x);
    }
  }

  determineNumSysAndCheckDigit(result, lgPatternFound);

  return rowOffset;
}

UPCEReader::Range UPCEReader::decodeEnd(Ref<BitArray> row, int endStart) {
  return findGuardPattern(row, endStart, true, MIDDLE_END_PATTERN);
}

bool UPCEReader::checkChecksum(Ref<String> const& s){
  return UPCEANReader::checkChecksum(convertUPCEtoUPCA(s));
}


bool UPCEReader::determineNumSysAndCheckDigit(std::string& resultString, int lgPatternFound) {
  for (int numSys = 0; numSys <= 1; numSys++) {
    for (int d = 0; d < 10; d++) {
      if (lgPatternFound == NUMSYS_AND_CHECK_DIGIT_PATTERNS[numSys][d]) {
        resultString.insert(0, 1, (char) ('0' + numSys));
        resultString.append(1, (char) ('0' + d));
        return true;
      }
    }
  }
  return false;
}

/**
 * Expands a UPC-E value back into its full, equivalent UPC-A code value.
 *
 * @param upce UPC-E code as string of digits
 * @return equivalent UPC-A code as string of digits
 */
Ref<String> UPCEReader::convertUPCEtoUPCA(Ref<String> const& upce_) {
  string const& upce(upce_->getText());
  string result;
  result.append(1, upce[0]);
  char lastChar = upce[6];
  switch (lastChar) {
  case '0':
  case '1':
  case '2':
    result.append(upce.substr(1,2));
    result.append(1, lastChar);
    result.append("0000");
    result.append(upce.substr(3,3));
    break;
  case '3':
    result.append(upce.substr(1,3));
    result.append("00000");
    result.append(upce.substr(4,2));
    break;
  case '4':
    result.append(upce.substr(1,4));
    result.append("00000");
    result.append(1, upce[5]);
    break;
  default:
    result.append(upce.substr(1,5));
    result.append("0000");
    result.append(1, lastChar);
    break;
  }
  result.append(1, upce[7]);
  return Ref<String>(new String(result));
}


zxing::BarcodeFormat UPCEReader::getBarcodeFormat() {
  return BarcodeFormat::UPC_E;
}
}
}

// file: zxing/pdf417/PDF417Reader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <zxing/pdf417/PDF417Reader.h>
// #include <zxing/pdf417/detector/Detector.h>

namespace zxing {
namespace pdf417 {
        
        
Ref<Result> PDF417Reader::decode(Ref<BinaryBitmap> image, DecodeHints hints) {
  Ref<DecoderResult> decoderResult;
  /* 2012-05-30 hfn C++ DecodeHintType does not yet know a type "PURE_BARCODE", */
  /* therefore skip this for now, todo: may be add this type later */
  /*
    if (!hints.isEmpty() && hints.containsKey(DecodeHintType.PURE_BARCODE)) {
    BitMatrix bits = extractPureBits(image.getBlackMatrix());
    decoderResult = decoder.decode(bits);
    points = NO_POINTS;
    } else {
  */
  detector::Detector detector(image);
  Ref<DetectorResult> detectorResult = detector.detect(hints); /* 2012-09-17 hints ("try_harder") */
  ArrayRef< Ref<ResultPoint> > points(detectorResult->getPoints());

  if (!hints.isEmpty()) {
    Ref<ResultPointCallback> rpcb = hints.getResultPointCallback();
    /* .get(DecodeHintType.NEED_RESULT_POINT_CALLBACK); */
    if (rpcb != NULL) {
      for (int i = 0; i < points->size(); i++) {
        rpcb->foundPossibleResultPoint(*points[i]);
      }
    }
  }
  decoderResult = decoder.decode(detectorResult->getBits(),hints);
  /*
    }
  */
  Ref<Result> r(new Result(decoderResult->getText(), decoderResult->getRawBytes(), points,
                           BarcodeFormat::PDF_417));
  return r;
}

void PDF417Reader::reset() {
  // do nothing
}

Ref<BitMatrix> PDF417Reader::extractPureBits(Ref<BitMatrix> image) {
  ArrayRef<int> leftTopBlack = image->getTopLeftOnBit();
  ArrayRef<int> rightBottomBlack = image->getBottomRightOnBit();
  /* see BitMatrix::getTopLeftOnBit etc.:
     if (leftTopBlack == null || rightBottomBlack == null) {
     throw NotFoundException.getNotFoundInstance();
     } */

  int nModuleSize = moduleSize(leftTopBlack, image);

  int top = leftTopBlack[1];
  int bottom = rightBottomBlack[1];
  int left = findPatternStart(leftTopBlack[0], top, image);
  int right = findPatternEnd(leftTopBlack[0], top, image);

  int matrixWidth = (right - left + 1) / nModuleSize;
  int matrixHeight = (bottom - top + 1) / nModuleSize;
  if (matrixWidth <= 0 || matrixHeight <= 0) {
    throw NotFoundException("PDF417Reader::extractPureBits: no matrix found!");
  }

  // Push in the "border" by half the module width so that we start
  // sampling in the middle of the module. Just in case the image is a
  // little off, this will help recover.
  int nudge = nModuleSize >> 1;
  top += nudge;
  left += nudge;

  // Now just read off the bits
  Ref<BitMatrix> bits(new BitMatrix(matrixWidth, matrixHeight));
  for (int y = 0; y < matrixHeight; y++) {
    int iOffset = top + y * nModuleSize;
    for (int x = 0; x < matrixWidth; x++) {
      if (image->get(left + x * nModuleSize, iOffset)) {
        bits->set(x, y);
      }
    }
  }
  return bits;
}

int PDF417Reader::moduleSize(ArrayRef<int> leftTopBlack, Ref<BitMatrix> image) {
  int x = leftTopBlack[0];
  int y = leftTopBlack[1];
  int width = image->getWidth();
  while (x < width && image->get(x, y)) {
    x++;
  }
  if (x == width) {
    throw NotFoundException("PDF417Reader::moduleSize: not found!");
  }

  int moduleSize = (int)(((unsigned)(x - leftTopBlack[0])) >> 3); // We've crossed left first bar, which is 8x
  if (moduleSize == 0) {
    throw NotFoundException("PDF417Reader::moduleSize: is zero!");
  }

  return moduleSize;
}

int PDF417Reader::findPatternStart(int x, int y, Ref<BitMatrix> image) {
  int width = image->getWidth();
  int start = x;
  // start should be on black
  int transitions = 0;
  bool black = true;
  while (start < width - 1 && transitions < 8) {
    start++;
    bool newBlack = image->get(start, y);
    if (black != newBlack) {
      transitions++;
    }
    black = newBlack;
  }
  if (start == width - 1) {
    throw NotFoundException("PDF417Reader::findPatternStart: no pattern start found!");
  }
  return start;
}

int PDF417Reader::findPatternEnd(int x, int y, Ref<BitMatrix> image) {
  int width = image->getWidth();
  int end = width - 1;
  // end should be on black
  while (end > x && !image->get(end, y)) {
    end--;
  }
  int transitions = 0;
  bool black = true;
  while (end > x && transitions < 9) {
    end--;
    bool newBlack = image->get(end, y);
    if (black != newBlack) {
      transitions++;
    }
    black = newBlack;
  }
  if (end == x) {
    throw NotFoundException("PDF417Reader::findPatternEnd: no pattern end found!");
  }
  return end;
}
}
}

// file: zxing/pdf417/decoder/BitMatrixParser.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 * Copyright 2008-2012 ZXing authors All rights reserved.
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
 * Modified by Hartmut Neubauer (HFN)
 *
 *   2012-06-27 HFN   plausibility checks of outer columns and modulus-3 conditions
 *                    of rows added.
 *   2012-09-?? HFN   because the Detector now counts the rows, there is no more
 *                    need to check the equality of consecutive rows. All rows are
 *                    parsed now.
 */

// #include <zxing/pdf417/decoder/BitMatrixParser.h>

namespace zxing {
namespace pdf417 {
namespace decoder {
    
const int BitMatrixParser::MAX_ROWS = 90;
// Maximum Codewords (Data + Error)
const int BitMatrixParser::MAX_CW_CAPACITY = 929;
const int BitMatrixParser::MODULES_IN_SYMBOL = 17;

BitMatrixParser::BitMatrixParser(Ref<BitMatrix> bitMatrix)
  : bitMatrix_(bitMatrix)
{
  rows_ = 0;
  leftColumnECData_ = 0;
  rightColumnECData_ = 0;
  for (int i = 0; i < 3; i++) {
    aLeftColumnTriple_[i]=0;
    aRightColumnTriple_[i]=0;
  }
  eraseCount_ = 0;
  ecLevel_ = -1;
}

/**
  * To ensure separability of rows, codewords of consecutive rows belong to
  * different subsets of all possible codewords. This routine scans the
  * symbols in the barcode. When it finds a number of consecutive rows which
  * are the same, it assumes that this is a row of codewords and processes
  * them into a codeword array.
  *
  * 2012-09-12 HFN: Because now, at an earlier stage, the Detector has counted
  * the rows, now it is no more necessary to check the equality of consecutive
  * rows. We now have to check every row.
  *
  * @return an array of codewords.
  * @throw FormatException for example if number of rows is too big or something
  * with row processing is bad
  */
ArrayRef<int> BitMatrixParser::readCodewords()
{
  //int width = bitMatrix_->getWidth();
  int height = bitMatrix_->getHeight();

  erasures_ = new Array<int>(MAX_CW_CAPACITY);

  ArrayRef<int> codewords (new Array<int>(MAX_CW_CAPACITY));
  int next = 0;
  int rowNumber = 0;
  for (int i = 0; i < height; i++) {
    if (rowNumber >= MAX_ROWS) {
      // Something is wrong, since we have exceeded
      // the maximum rows in the specification.
      throw FormatException("BitMatrixParser::readCodewords(PDF): Too many rows!");
    }
    // Process Row
    next = processRow(rowNumber, codewords, next);
    rowNumber++;
  }
  erasures_ = trimArray(erasures_, eraseCount_);
  return trimArray(codewords, next);
}

/**
 * Convert the symbols in the row to codewords.
 * Each PDF417 symbol character consists of four bar elements and four space
 * elements, each of which can be one to six modules wide. The four bar and
 * four space elements shall measure 17 modules in total.
 *
 * @param rowNumber   the current row number of codewords.
 * @param codewords   the codeword array to save codewords into.
 * @param next        the next available index into the codewords array.
 * @return the next available index into the codeword array after processing
 *         this row.
 */
int BitMatrixParser::processRow(int rowNumber, ArrayRef<int> codewords, int next) {
  int width = bitMatrix_->getWidth();
  int columnNumber = 0;
  int cwClusterNumber = -1;
  int64_t symbol = 0;
  for (int i = 0; i < width; i += MODULES_IN_SYMBOL) {
    for (int mask = MODULES_IN_SYMBOL - 1; mask >= 0; mask--) {
      if (bitMatrix_->get(i + (MODULES_IN_SYMBOL - 1 - mask), rowNumber)) {
        symbol |= int64_t(1) << mask;
      }
    }
    if (columnNumber > 0) {
      cwClusterNumber = -1;
      int cw = getCodeword(symbol,&cwClusterNumber);

      // 2012-06-27 HFN: cwClusterNumber should be the modulus of the row number by 3; otherwise,
      // handle the codeword as erasure:
      if ((cwClusterNumber >= 0) && (cwClusterNumber != rowNumber % 3)) {
        cw = -1;
      }

      if (cw < 0 && i < width - MODULES_IN_SYMBOL) {
        // Skip errors on the Right row indicator column
        if (eraseCount_ >= (int)erasures_->size()) {
          throw FormatException("BitMatrixParser::processRow(PDF417): eraseCount too big!");
        }
        erasures_[eraseCount_] = next;
        next++;
        eraseCount_++;
      } else {
        if (next >= codewords->size()) {
          throw FormatException("BitMatrixParser::processRow(PDF417): codewords index out of bound.");
        }
        codewords[next++] = cw;
      }
    } else {
      // Left row indicator column
      cwClusterNumber = -1;
      int cw = getCodeword(symbol,&cwClusterNumber);
      aLeftColumnTriple_[rowNumber % 3] = cw; /* added 2012-06-22 hfn */
      if (ecLevel_ < 0 && rowNumber % 3 == 1) {
        leftColumnECData_ = cw;
      }
    }
    symbol = 0;
    columnNumber++;
  }
  if (columnNumber > 1) {
    // Right row indicator column is in codeword[next]
    // Overwrite the last codeword i.e. Right Row Indicator
    --next;
    aRightColumnTriple_[rowNumber % 3] = codewords[next]; /* added 2012-06-22 hfn */
    if (rowNumber % 3 == 2) {
      if (ecLevel_ < 0) {
        rightColumnECData_ = codewords[next];
        if (rightColumnECData_ == leftColumnECData_ && (int)leftColumnECData_ > 0) {  /* leftColumnECData_ != 0 */
          ecLevel_ = ((rightColumnECData_ % 30) - rows_ % 3) / 3;
        }
      }
      // 2012-06-22 hfn: verify whether outer columns are still okay:
      if (!VerifyOuterColumns(rowNumber)) {
        throw FormatException("BitMatrixParser::processRow(PDF417): outer columns corrupted!");
      }
    }
    codewords[next] = 0;
  }
  return next;
}

/* Static methods. */

/**
  * Trim the array to the required size.
  *
  * @param array the array
  * @param size  the size to trim it to
  * @return the new trimmed array
  */
ArrayRef<int> BitMatrixParser::trimArray(ArrayRef<int> array, int size)
{
  if (size < 0) {
    throw IllegalArgumentException("BitMatrixParser::trimArray: negative size!");
  }
  // 2012-10-12 hfn don't throw "NoErrorException" when size == 0
  ArrayRef<int> a = new Array<int>(size);
  for (int i = 0; i < size; i++) {
    a[i] = array[i];
  }
  return a;
}

/**
  * Translate the symbol into a codeword.
  *
  * @param symbol
  * @return the codeword corresponding to the symbol.
  */

/**
  * 2012-06-27 hfn With the second argument, it is possible to verify in which of the three
  * "blocks" of the codeword table the codeword has been found: 0, 1 or 2.
  */
int BitMatrixParser::getCodeword(int64_t symbol, int *pi)
{
  int64_t sym = symbol & 0x3FFFF;
  int i = findCodewordIndex(sym);
  if (i == -1) {
    return -1;
  } else {
    int cw = CODEWORD_TABLE[i] - 1;
    if (pi!= NULL) {
      *pi = cw / 929;
    }
    cw %= 929;
    return cw;
  }
}

/**
  * Use a binary search to find the index of the codeword corresponding to
  * this symbol.
  *
  * @param symbol the symbol from the barcode.
  * @return the index into the codeword table.
  */
int BitMatrixParser::findCodewordIndex(int64_t symbol)
{
  int first = 0;
  int upto = SYMBOL_TABLE_LENGTH;
  while (first < upto) {
    int mid = ((unsigned int)(first + upto)) >> 1; // Compute mid point.
    if (symbol < SYMBOL_TABLE[mid]) {
      upto = mid; // repeat search in bottom half.
    } else if (symbol > SYMBOL_TABLE[mid]) {
      first = mid + 1; // Repeat search in top half.
    } else {
      return mid; // Found it. return position
    }
  }
  return -1;
}

/*
 * 2012-06-22 hfn additional verification of outer columns
 */
bool BitMatrixParser::VerifyOuterColumns(int rownumber)
{
  return IsEqual(aLeftColumnTriple_[0], aRightColumnTriple_[1], rownumber)
      && IsEqual(aLeftColumnTriple_[1], aRightColumnTriple_[2], rownumber)
      && IsEqual(aLeftColumnTriple_[2], aRightColumnTriple_[0], rownumber);
}

/*
 * Verifies whether two codewords are equal or at least one of the codewords has not
 * been recognized.
 */
bool BitMatrixParser::IsEqual(int &a, int &b, int rownumber)
{
  int ret = (a == b) || (a == -1) || (b == -1);
  if (!ret) {
    int row3 = rownumber / 3;
    int row30 = row3 * 30;
    int row59 = row30 + 29;
    if (a < row30 || a > row59) {
      a = -1;
    }
    if (b < row30 || b > row59) {
      b = -1;
    }
  }
  return true;
}

const int BitMatrixParser::SYMBOL_TABLE[] =
{
  0x1025e, 0x1027a, 0x1029e,
  0x102bc, 0x102f2, 0x102f4, 0x1032e, 0x1034e, 0x1035c, 0x10396,
  0x103a6, 0x103ac, 0x10422, 0x10428, 0x10436, 0x10442, 0x10444,
  0x10448, 0x10450, 0x1045e, 0x10466, 0x1046c, 0x1047a, 0x10482,
  0x1049e, 0x104a0, 0x104bc, 0x104c6, 0x104d8, 0x104ee, 0x104f2,
  0x104f4, 0x10504, 0x10508, 0x10510, 0x1051e, 0x10520, 0x1053c,
  0x10540, 0x10578, 0x10586, 0x1058c, 0x10598, 0x105b0, 0x105be,
  0x105ce, 0x105dc, 0x105e2, 0x105e4, 0x105e8, 0x105f6, 0x1062e,
  0x1064e, 0x1065c, 0x1068e, 0x1069c, 0x106b8, 0x106de, 0x106fa,
  0x10716, 0x10726, 0x1072c, 0x10746, 0x1074c, 0x10758, 0x1076e,
  0x10792, 0x10794, 0x107a2, 0x107a4, 0x107a8, 0x107b6, 0x10822,
  0x10828, 0x10842, 0x10848, 0x10850, 0x1085e, 0x10866, 0x1086c,
  0x1087a, 0x10882, 0x10884, 0x10890, 0x1089e, 0x108a0, 0x108bc,
  0x108c6, 0x108cc, 0x108d8, 0x108ee, 0x108f2, 0x108f4, 0x10902,
  0x10908, 0x1091e, 0x10920, 0x1093c, 0x10940, 0x10978, 0x10986,
  0x10998, 0x109b0, 0x109be, 0x109ce, 0x109dc, 0x109e2, 0x109e4,
  0x109e8, 0x109f6, 0x10a08, 0x10a10, 0x10a1e, 0x10a20, 0x10a3c,
  0x10a40, 0x10a78, 0x10af0, 0x10b06, 0x10b0c, 0x10b18, 0x10b30,
  0x10b3e, 0x10b60, 0x10b7c, 0x10b8e, 0x10b9c, 0x10bb8, 0x10bc2,
  0x10bc4, 0x10bc8, 0x10bd0, 0x10bde, 0x10be6, 0x10bec, 0x10c2e,
  0x10c4e, 0x10c5c, 0x10c62, 0x10c64, 0x10c68, 0x10c76, 0x10c8e,
  0x10c9c, 0x10cb8, 0x10cc2, 0x10cc4, 0x10cc8, 0x10cd0, 0x10cde,
  0x10ce6, 0x10cec, 0x10cfa, 0x10d0e, 0x10d1c, 0x10d38, 0x10d70,
  0x10d7e, 0x10d82, 0x10d84, 0x10d88, 0x10d90, 0x10d9e, 0x10da0,
  0x10dbc, 0x10dc6, 0x10dcc, 0x10dd8, 0x10dee, 0x10df2, 0x10df4,
  0x10e16, 0x10e26, 0x10e2c, 0x10e46, 0x10e58, 0x10e6e, 0x10e86,
  0x10e8c, 0x10e98, 0x10eb0, 0x10ebe, 0x10ece, 0x10edc, 0x10f0a,
  0x10f12, 0x10f14, 0x10f22, 0x10f28, 0x10f36, 0x10f42, 0x10f44,
  0x10f48, 0x10f50, 0x10f5e, 0x10f66, 0x10f6c, 0x10fb2, 0x10fb4,
  0x11022, 0x11028, 0x11042, 0x11048, 0x11050, 0x1105e, 0x1107a,
  0x11082, 0x11084, 0x11090, 0x1109e, 0x110a0, 0x110bc, 0x110c6,
  0x110cc, 0x110d8, 0x110ee, 0x110f2, 0x110f4, 0x11102, 0x1111e,
  0x11120, 0x1113c, 0x11140, 0x11178, 0x11186, 0x11198, 0x111b0,
  0x111be, 0x111ce, 0x111dc, 0x111e2, 0x111e4, 0x111e8, 0x111f6,
  0x11208, 0x1121e, 0x11220, 0x11278, 0x112f0, 0x1130c, 0x11330,
  0x1133e, 0x11360, 0x1137c, 0x1138e, 0x1139c, 0x113b8, 0x113c2,
  0x113c8, 0x113d0, 0x113de, 0x113e6, 0x113ec, 0x11408, 0x11410,
  0x1141e, 0x11420, 0x1143c, 0x11440, 0x11478, 0x114f0, 0x115e0,
  0x1160c, 0x11618, 0x11630, 0x1163e, 0x11660, 0x1167c, 0x116c0,
  0x116f8, 0x1171c, 0x11738, 0x11770, 0x1177e, 0x11782, 0x11784,
  0x11788, 0x11790, 0x1179e, 0x117a0, 0x117bc, 0x117c6, 0x117cc,
  0x117d8, 0x117ee, 0x1182e, 0x11834, 0x1184e, 0x1185c, 0x11862,
  0x11864, 0x11868, 0x11876, 0x1188e, 0x1189c, 0x118b8, 0x118c2,
  0x118c8, 0x118d0, 0x118de, 0x118e6, 0x118ec, 0x118fa, 0x1190e,
  0x1191c, 0x11938, 0x11970, 0x1197e, 0x11982, 0x11984, 0x11990,
  0x1199e, 0x119a0, 0x119bc, 0x119c6, 0x119cc, 0x119d8, 0x119ee,
  0x119f2, 0x119f4, 0x11a0e, 0x11a1c, 0x11a38, 0x11a70, 0x11a7e,
  0x11ae0, 0x11afc, 0x11b08, 0x11b10, 0x11b1e, 0x11b20, 0x11b3c,
  0x11b40, 0x11b78, 0x11b8c, 0x11b98, 0x11bb0, 0x11bbe, 0x11bce,
  0x11bdc, 0x11be2, 0x11be4, 0x11be8, 0x11bf6, 0x11c16, 0x11c26,
  0x11c2c, 0x11c46, 0x11c4c, 0x11c58, 0x11c6e, 0x11c86, 0x11c98,
  0x11cb0, 0x11cbe, 0x11cce, 0x11cdc, 0x11ce2, 0x11ce4, 0x11ce8,
  0x11cf6, 0x11d06, 0x11d0c, 0x11d18, 0x11d30, 0x11d3e, 0x11d60,
  0x11d7c, 0x11d8e, 0x11d9c, 0x11db8, 0x11dc4, 0x11dc8, 0x11dd0,
  0x11dde, 0x11de6, 0x11dec, 0x11dfa, 0x11e0a, 0x11e12, 0x11e14,
  0x11e22, 0x11e24, 0x11e28, 0x11e36, 0x11e42, 0x11e44, 0x11e50,
  0x11e5e, 0x11e66, 0x11e6c, 0x11e82, 0x11e84, 0x11e88, 0x11e90,
  0x11e9e, 0x11ea0, 0x11ebc, 0x11ec6, 0x11ecc, 0x11ed8, 0x11eee,
  0x11f1a, 0x11f2e, 0x11f32, 0x11f34, 0x11f4e, 0x11f5c, 0x11f62,
  0x11f64, 0x11f68, 0x11f76, 0x12048, 0x1205e, 0x12082, 0x12084,
  0x12090, 0x1209e, 0x120a0, 0x120bc, 0x120d8, 0x120f2, 0x120f4,
  0x12108, 0x1211e, 0x12120, 0x1213c, 0x12140, 0x12178, 0x12186,
  0x12198, 0x121b0, 0x121be, 0x121e2, 0x121e4, 0x121e8, 0x121f6,
  0x12204, 0x12210, 0x1221e, 0x12220, 0x12278, 0x122f0, 0x12306,
  0x1230c, 0x12330, 0x1233e, 0x12360, 0x1237c, 0x1238e, 0x1239c,
  0x123b8, 0x123c2, 0x123c8, 0x123d0, 0x123e6, 0x123ec, 0x1241e,
  0x12420, 0x1243c, 0x124f0, 0x125e0, 0x12618, 0x1263e, 0x12660,
  0x1267c, 0x126c0, 0x126f8, 0x12738, 0x12770, 0x1277e, 0x12782,
  0x12784, 0x12790, 0x1279e, 0x127a0, 0x127bc, 0x127c6, 0x127cc,
  0x127d8, 0x127ee, 0x12820, 0x1283c, 0x12840, 0x12878, 0x128f0,
  0x129e0, 0x12bc0, 0x12c18, 0x12c30, 0x12c3e, 0x12c60, 0x12c7c,
  0x12cc0, 0x12cf8, 0x12df0, 0x12e1c, 0x12e38, 0x12e70, 0x12e7e,
  0x12ee0, 0x12efc, 0x12f04, 0x12f08, 0x12f10, 0x12f20, 0x12f3c,
  0x12f40, 0x12f78, 0x12f86, 0x12f8c, 0x12f98, 0x12fb0, 0x12fbe,
  0x12fce, 0x12fdc, 0x1302e, 0x1304e, 0x1305c, 0x13062, 0x13068,
  0x1308e, 0x1309c, 0x130b8, 0x130c2, 0x130c8, 0x130d0, 0x130de,
  0x130ec, 0x130fa, 0x1310e, 0x13138, 0x13170, 0x1317e, 0x13182,
  0x13184, 0x13190, 0x1319e, 0x131a0, 0x131bc, 0x131c6, 0x131cc,
  0x131d8, 0x131f2, 0x131f4, 0x1320e, 0x1321c, 0x13270, 0x1327e,
  0x132e0, 0x132fc, 0x13308, 0x1331e, 0x13320, 0x1333c, 0x13340,
  0x13378, 0x13386, 0x13398, 0x133b0, 0x133be, 0x133ce, 0x133dc,
  0x133e2, 0x133e4, 0x133e8, 0x133f6, 0x1340e, 0x1341c, 0x13438,
  0x13470, 0x1347e, 0x134e0, 0x134fc, 0x135c0, 0x135f8, 0x13608,
  0x13610, 0x1361e, 0x13620, 0x1363c, 0x13640, 0x13678, 0x136f0,
  0x1370c, 0x13718, 0x13730, 0x1373e, 0x13760, 0x1377c, 0x1379c,
  0x137b8, 0x137c2, 0x137c4, 0x137c8, 0x137d0, 0x137de, 0x137e6,
  0x137ec, 0x13816, 0x13826, 0x1382c, 0x13846, 0x1384c, 0x13858,
  0x1386e, 0x13874, 0x13886, 0x13898, 0x138b0, 0x138be, 0x138ce,
  0x138dc, 0x138e2, 0x138e4, 0x138e8, 0x13906, 0x1390c, 0x13930,
  0x1393e, 0x13960, 0x1397c, 0x1398e, 0x1399c, 0x139b8, 0x139c8,
  0x139d0, 0x139de, 0x139e6, 0x139ec, 0x139fa, 0x13a06, 0x13a0c,
  0x13a18, 0x13a30, 0x13a3e, 0x13a60, 0x13a7c, 0x13ac0, 0x13af8,
  0x13b0e, 0x13b1c, 0x13b38, 0x13b70, 0x13b7e, 0x13b88, 0x13b90,
  0x13b9e, 0x13ba0, 0x13bbc, 0x13bcc, 0x13bd8, 0x13bee, 0x13bf2,
  0x13bf4, 0x13c12, 0x13c14, 0x13c22, 0x13c24, 0x13c28, 0x13c36,
  0x13c42, 0x13c48, 0x13c50, 0x13c5e, 0x13c66, 0x13c6c, 0x13c82,
  0x13c84, 0x13c90, 0x13c9e, 0x13ca0, 0x13cbc, 0x13cc6, 0x13ccc,
  0x13cd8, 0x13cee, 0x13d02, 0x13d04, 0x13d08, 0x13d10, 0x13d1e,
  0x13d20, 0x13d3c, 0x13d40, 0x13d78, 0x13d86, 0x13d8c, 0x13d98,
  0x13db0, 0x13dbe, 0x13dce, 0x13ddc, 0x13de4, 0x13de8, 0x13df6,
  0x13e1a, 0x13e2e, 0x13e32, 0x13e34, 0x13e4e, 0x13e5c, 0x13e62,
  0x13e64, 0x13e68, 0x13e76, 0x13e8e, 0x13e9c, 0x13eb8, 0x13ec2,
  0x13ec4, 0x13ec8, 0x13ed0, 0x13ede, 0x13ee6, 0x13eec, 0x13f26,
  0x13f2c, 0x13f3a, 0x13f46, 0x13f4c, 0x13f58, 0x13f6e, 0x13f72,
  0x13f74, 0x14082, 0x1409e, 0x140a0, 0x140bc, 0x14104, 0x14108,
  0x14110, 0x1411e, 0x14120, 0x1413c, 0x14140, 0x14178, 0x1418c,
  0x14198, 0x141b0, 0x141be, 0x141e2, 0x141e4, 0x141e8, 0x14208,
  0x14210, 0x1421e, 0x14220, 0x1423c, 0x14240, 0x14278, 0x142f0,
  0x14306, 0x1430c, 0x14318, 0x14330, 0x1433e, 0x14360, 0x1437c,
  0x1438e, 0x143c2, 0x143c4, 0x143c8, 0x143d0, 0x143e6, 0x143ec,
  0x14408, 0x14410, 0x1441e, 0x14420, 0x1443c, 0x14440, 0x14478,
  0x144f0, 0x145e0, 0x1460c, 0x14618, 0x14630, 0x1463e, 0x14660,
  0x1467c, 0x146c0, 0x146f8, 0x1471c, 0x14738, 0x14770, 0x1477e,
  0x14782, 0x14784, 0x14788, 0x14790, 0x147a0, 0x147bc, 0x147c6,
  0x147cc, 0x147d8, 0x147ee, 0x14810, 0x14820, 0x1483c, 0x14840,
  0x14878, 0x148f0, 0x149e0, 0x14bc0, 0x14c30, 0x14c3e, 0x14c60,
  0x14c7c, 0x14cc0, 0x14cf8, 0x14df0, 0x14e38, 0x14e70, 0x14e7e,
  0x14ee0, 0x14efc, 0x14f04, 0x14f08, 0x14f10, 0x14f1e, 0x14f20,
  0x14f3c, 0x14f40, 0x14f78, 0x14f86, 0x14f8c, 0x14f98, 0x14fb0,
  0x14fce, 0x14fdc, 0x15020, 0x15040, 0x15078, 0x150f0, 0x151e0,
  0x153c0, 0x15860, 0x1587c, 0x158c0, 0x158f8, 0x159f0, 0x15be0,
  0x15c70, 0x15c7e, 0x15ce0, 0x15cfc, 0x15dc0, 0x15df8, 0x15e08,
  0x15e10, 0x15e20, 0x15e40, 0x15e78, 0x15ef0, 0x15f0c, 0x15f18,
  0x15f30, 0x15f60, 0x15f7c, 0x15f8e, 0x15f9c, 0x15fb8, 0x1604e,
  0x1605c, 0x1608e, 0x1609c, 0x160b8, 0x160c2, 0x160c4, 0x160c8,
  0x160de, 0x1610e, 0x1611c, 0x16138, 0x16170, 0x1617e, 0x16184,
  0x16188, 0x16190, 0x1619e, 0x161a0, 0x161bc, 0x161c6, 0x161cc,
  0x161d8, 0x161f2, 0x161f4, 0x1620e, 0x1621c, 0x16238, 0x16270,
  0x1627e, 0x162e0, 0x162fc, 0x16304, 0x16308, 0x16310, 0x1631e,
  0x16320, 0x1633c, 0x16340, 0x16378, 0x16386, 0x1638c, 0x16398,
  0x163b0, 0x163be, 0x163ce, 0x163dc, 0x163e2, 0x163e4, 0x163e8,
  0x163f6, 0x1640e, 0x1641c, 0x16438, 0x16470, 0x1647e, 0x164e0,
  0x164fc, 0x165c0, 0x165f8, 0x16610, 0x1661e, 0x16620, 0x1663c,
  0x16640, 0x16678, 0x166f0, 0x16718, 0x16730, 0x1673e, 0x16760,
  0x1677c, 0x1678e, 0x1679c, 0x167b8, 0x167c2, 0x167c4, 0x167c8,
  0x167d0, 0x167de, 0x167e6, 0x167ec, 0x1681c, 0x16838, 0x16870,
  0x168e0, 0x168fc, 0x169c0, 0x169f8, 0x16bf0, 0x16c10, 0x16c1e,
  0x16c20, 0x16c3c, 0x16c40, 0x16c78, 0x16cf0, 0x16de0, 0x16e18,
  0x16e30, 0x16e3e, 0x16e60, 0x16e7c, 0x16ec0, 0x16ef8, 0x16f1c,
  0x16f38, 0x16f70, 0x16f7e, 0x16f84, 0x16f88, 0x16f90, 0x16f9e,
  0x16fa0, 0x16fbc, 0x16fc6, 0x16fcc, 0x16fd8, 0x17026, 0x1702c,
  0x17046, 0x1704c, 0x17058, 0x1706e, 0x17086, 0x1708c, 0x17098,
  0x170b0, 0x170be, 0x170ce, 0x170dc, 0x170e8, 0x17106, 0x1710c,
  0x17118, 0x17130, 0x1713e, 0x17160, 0x1717c, 0x1718e, 0x1719c,
  0x171b8, 0x171c2, 0x171c4, 0x171c8, 0x171d0, 0x171de, 0x171e6,
  0x171ec, 0x171fa, 0x17206, 0x1720c, 0x17218, 0x17230, 0x1723e,
  0x17260, 0x1727c, 0x172c0, 0x172f8, 0x1730e, 0x1731c, 0x17338,
  0x17370, 0x1737e, 0x17388, 0x17390, 0x1739e, 0x173a0, 0x173bc,
  0x173cc, 0x173d8, 0x173ee, 0x173f2, 0x173f4, 0x1740c, 0x17418,
  0x17430, 0x1743e, 0x17460, 0x1747c, 0x174c0, 0x174f8, 0x175f0,
  0x1760e, 0x1761c, 0x17638, 0x17670, 0x1767e, 0x176e0, 0x176fc,
  0x17708, 0x17710, 0x1771e, 0x17720, 0x1773c, 0x17740, 0x17778,
  0x17798, 0x177b0, 0x177be, 0x177dc, 0x177e2, 0x177e4, 0x177e8,
  0x17822, 0x17824, 0x17828, 0x17836, 0x17842, 0x17844, 0x17848,
  0x17850, 0x1785e, 0x17866, 0x1786c, 0x17882, 0x17884, 0x17888,
  0x17890, 0x1789e, 0x178a0, 0x178bc, 0x178c6, 0x178cc, 0x178d8,
  0x178ee, 0x178f2, 0x178f4, 0x17902, 0x17904, 0x17908, 0x17910,
  0x1791e, 0x17920, 0x1793c, 0x17940, 0x17978, 0x17986, 0x1798c,
  0x17998, 0x179b0, 0x179be, 0x179ce, 0x179dc, 0x179e2, 0x179e4,
  0x179e8, 0x179f6, 0x17a04, 0x17a08, 0x17a10, 0x17a1e, 0x17a20,
  0x17a3c, 0x17a40, 0x17a78, 0x17af0, 0x17b06, 0x17b0c, 0x17b18,
  0x17b30, 0x17b3e, 0x17b60, 0x17b7c, 0x17b8e, 0x17b9c, 0x17bb8,
  0x17bc4, 0x17bc8, 0x17bd0, 0x17bde, 0x17be6, 0x17bec, 0x17c2e,
  0x17c32, 0x17c34, 0x17c4e, 0x17c5c, 0x17c62, 0x17c64, 0x17c68,
  0x17c76, 0x17c8e, 0x17c9c, 0x17cb8, 0x17cc2, 0x17cc4, 0x17cc8,
  0x17cd0, 0x17cde, 0x17ce6, 0x17cec, 0x17d0e, 0x17d1c, 0x17d38,
  0x17d70, 0x17d82, 0x17d84, 0x17d88, 0x17d90, 0x17d9e, 0x17da0,
  0x17dbc, 0x17dc6, 0x17dcc, 0x17dd8, 0x17dee, 0x17e26, 0x17e2c,
  0x17e3a, 0x17e46, 0x17e4c, 0x17e58, 0x17e6e, 0x17e72, 0x17e74,
  0x17e86, 0x17e8c, 0x17e98, 0x17eb0, 0x17ece, 0x17edc, 0x17ee2,
  0x17ee4, 0x17ee8, 0x17ef6, 0x1813a, 0x18172, 0x18174, 0x18216,
  0x18226, 0x1823a, 0x1824c, 0x18258, 0x1826e, 0x18272, 0x18274,
  0x18298, 0x182be, 0x182e2, 0x182e4, 0x182e8, 0x182f6, 0x1835e,
  0x1837a, 0x183ae, 0x183d6, 0x18416, 0x18426, 0x1842c, 0x1843a,
  0x18446, 0x18458, 0x1846e, 0x18472, 0x18474, 0x18486, 0x184b0,
  0x184be, 0x184ce, 0x184dc, 0x184e2, 0x184e4, 0x184e8, 0x184f6,
  0x18506, 0x1850c, 0x18518, 0x18530, 0x1853e, 0x18560, 0x1857c,
  0x1858e, 0x1859c, 0x185b8, 0x185c2, 0x185c4, 0x185c8, 0x185d0,
  0x185de, 0x185e6, 0x185ec, 0x185fa, 0x18612, 0x18614, 0x18622,
  0x18628, 0x18636, 0x18642, 0x18650, 0x1865e, 0x1867a, 0x18682,
  0x18684, 0x18688, 0x18690, 0x1869e, 0x186a0, 0x186bc, 0x186c6,
  0x186cc, 0x186d8, 0x186ee, 0x186f2, 0x186f4, 0x1872e, 0x1874e,
  0x1875c, 0x18796, 0x187a6, 0x187ac, 0x187d2, 0x187d4, 0x18826,
  0x1882c, 0x1883a, 0x18846, 0x1884c, 0x18858, 0x1886e, 0x18872,
  0x18874, 0x18886, 0x18898, 0x188b0, 0x188be, 0x188ce, 0x188dc,
  0x188e2, 0x188e4, 0x188e8, 0x188f6, 0x1890c, 0x18930, 0x1893e,
  0x18960, 0x1897c, 0x1898e, 0x189b8, 0x189c2, 0x189c8, 0x189d0,
  0x189de, 0x189e6, 0x189ec, 0x189fa, 0x18a18, 0x18a30, 0x18a3e,
  0x18a60, 0x18a7c, 0x18ac0, 0x18af8, 0x18b1c, 0x18b38, 0x18b70,
  0x18b7e, 0x18b82, 0x18b84, 0x18b88, 0x18b90, 0x18b9e, 0x18ba0,
  0x18bbc, 0x18bc6, 0x18bcc, 0x18bd8, 0x18bee, 0x18bf2, 0x18bf4,
  0x18c22, 0x18c24, 0x18c28, 0x18c36, 0x18c42, 0x18c48, 0x18c50,
  0x18c5e, 0x18c66, 0x18c7a, 0x18c82, 0x18c84, 0x18c90, 0x18c9e,
  0x18ca0, 0x18cbc, 0x18ccc, 0x18cf2, 0x18cf4, 0x18d04, 0x18d08,
  0x18d10, 0x18d1e, 0x18d20, 0x18d3c, 0x18d40, 0x18d78, 0x18d86,
  0x18d98, 0x18dce, 0x18de2, 0x18de4, 0x18de8, 0x18e2e, 0x18e32,
  0x18e34, 0x18e4e, 0x18e5c, 0x18e62, 0x18e64, 0x18e68, 0x18e8e,
  0x18e9c, 0x18eb8, 0x18ec2, 0x18ec4, 0x18ec8, 0x18ed0, 0x18efa,
  0x18f16, 0x18f26, 0x18f2c, 0x18f46, 0x18f4c, 0x18f58, 0x18f6e,
  0x18f8a, 0x18f92, 0x18f94, 0x18fa2, 0x18fa4, 0x18fa8, 0x18fb6,
  0x1902c, 0x1903a, 0x19046, 0x1904c, 0x19058, 0x19072, 0x19074,
  0x19086, 0x19098, 0x190b0, 0x190be, 0x190ce, 0x190dc, 0x190e2,
  0x190e8, 0x190f6, 0x19106, 0x1910c, 0x19130, 0x1913e, 0x19160,
  0x1917c, 0x1918e, 0x1919c, 0x191b8, 0x191c2, 0x191c8, 0x191d0,
  0x191de, 0x191e6, 0x191ec, 0x191fa, 0x19218, 0x1923e, 0x19260,
  0x1927c, 0x192c0, 0x192f8, 0x19338, 0x19370, 0x1937e, 0x19382,
  0x19384, 0x19390, 0x1939e, 0x193a0, 0x193bc, 0x193c6, 0x193cc,
  0x193d8, 0x193ee, 0x193f2, 0x193f4, 0x19430, 0x1943e, 0x19460,
  0x1947c, 0x194c0, 0x194f8, 0x195f0, 0x19638, 0x19670, 0x1967e,
  0x196e0, 0x196fc, 0x19702, 0x19704, 0x19708, 0x19710, 0x19720,
  0x1973c, 0x19740, 0x19778, 0x19786, 0x1978c, 0x19798, 0x197b0,
  0x197be, 0x197ce, 0x197dc, 0x197e2, 0x197e4, 0x197e8, 0x19822,
  0x19824, 0x19842, 0x19848, 0x19850, 0x1985e, 0x19866, 0x1987a,
  0x19882, 0x19884, 0x19890, 0x1989e, 0x198a0, 0x198bc, 0x198cc,
  0x198f2, 0x198f4, 0x19902, 0x19908, 0x1991e, 0x19920, 0x1993c,
  0x19940, 0x19978, 0x19986, 0x19998, 0x199ce, 0x199e2, 0x199e4,
  0x199e8, 0x19a08, 0x19a10, 0x19a1e, 0x19a20, 0x19a3c, 0x19a40,
  0x19a78, 0x19af0, 0x19b18, 0x19b3e, 0x19b60, 0x19b9c, 0x19bc2,
  0x19bc4, 0x19bc8, 0x19bd0, 0x19be6, 0x19c2e, 0x19c34, 0x19c4e,
  0x19c5c, 0x19c62, 0x19c64, 0x19c68, 0x19c8e, 0x19c9c, 0x19cb8,
  0x19cc2, 0x19cc8, 0x19cd0, 0x19ce6, 0x19cfa, 0x19d0e, 0x19d1c,
  0x19d38, 0x19d70, 0x19d7e, 0x19d82, 0x19d84, 0x19d88, 0x19d90,
  0x19da0, 0x19dcc, 0x19df2, 0x19df4, 0x19e16, 0x19e26, 0x19e2c,
  0x19e46, 0x19e4c, 0x19e58, 0x19e74, 0x19e86, 0x19e8c, 0x19e98,
  0x19eb0, 0x19ebe, 0x19ece, 0x19ee2, 0x19ee4, 0x19ee8, 0x19f0a,
  0x19f12, 0x19f14, 0x19f22, 0x19f24, 0x19f28, 0x19f42, 0x19f44,
  0x19f48, 0x19f50, 0x19f5e, 0x19f6c, 0x19f9a, 0x19fae, 0x19fb2,
  0x19fb4, 0x1a046, 0x1a04c, 0x1a072, 0x1a074, 0x1a086, 0x1a08c,
  0x1a098, 0x1a0b0, 0x1a0be, 0x1a0e2, 0x1a0e4, 0x1a0e8, 0x1a0f6,
  0x1a106, 0x1a10c, 0x1a118, 0x1a130, 0x1a13e, 0x1a160, 0x1a17c,
  0x1a18e, 0x1a19c, 0x1a1b8, 0x1a1c2, 0x1a1c4, 0x1a1c8, 0x1a1d0,
  0x1a1de, 0x1a1e6, 0x1a1ec, 0x1a218, 0x1a230, 0x1a23e, 0x1a260,
  0x1a27c, 0x1a2c0, 0x1a2f8, 0x1a31c, 0x1a338, 0x1a370, 0x1a37e,
  0x1a382, 0x1a384, 0x1a388, 0x1a390, 0x1a39e, 0x1a3a0, 0x1a3bc,
  0x1a3c6, 0x1a3cc, 0x1a3d8, 0x1a3ee, 0x1a3f2, 0x1a3f4, 0x1a418,
  0x1a430, 0x1a43e, 0x1a460, 0x1a47c, 0x1a4c0, 0x1a4f8, 0x1a5f0,
  0x1a61c, 0x1a638, 0x1a670, 0x1a67e, 0x1a6e0, 0x1a6fc, 0x1a702,
  0x1a704, 0x1a708, 0x1a710, 0x1a71e, 0x1a720, 0x1a73c, 0x1a740,
  0x1a778, 0x1a786, 0x1a78c, 0x1a798, 0x1a7b0, 0x1a7be, 0x1a7ce,
  0x1a7dc, 0x1a7e2, 0x1a7e4, 0x1a7e8, 0x1a830, 0x1a860, 0x1a87c,
  0x1a8c0, 0x1a8f8, 0x1a9f0, 0x1abe0, 0x1ac70, 0x1ac7e, 0x1ace0,
  0x1acfc, 0x1adc0, 0x1adf8, 0x1ae04, 0x1ae08, 0x1ae10, 0x1ae20,
  0x1ae3c, 0x1ae40, 0x1ae78, 0x1aef0, 0x1af06, 0x1af0c, 0x1af18,
  0x1af30, 0x1af3e, 0x1af60, 0x1af7c, 0x1af8e, 0x1af9c, 0x1afb8,
  0x1afc4, 0x1afc8, 0x1afd0, 0x1afde, 0x1b042, 0x1b05e, 0x1b07a,
  0x1b082, 0x1b084, 0x1b088, 0x1b090, 0x1b09e, 0x1b0a0, 0x1b0bc,
  0x1b0cc, 0x1b0f2, 0x1b0f4, 0x1b102, 0x1b104, 0x1b108, 0x1b110,
  0x1b11e, 0x1b120, 0x1b13c, 0x1b140, 0x1b178, 0x1b186, 0x1b198,
  0x1b1ce, 0x1b1e2, 0x1b1e4, 0x1b1e8, 0x1b204, 0x1b208, 0x1b210,
  0x1b21e, 0x1b220, 0x1b23c, 0x1b240, 0x1b278, 0x1b2f0, 0x1b30c,
  0x1b33e, 0x1b360, 0x1b39c, 0x1b3c2, 0x1b3c4, 0x1b3c8, 0x1b3d0,
  0x1b3e6, 0x1b410, 0x1b41e, 0x1b420, 0x1b43c, 0x1b440, 0x1b478,
  0x1b4f0, 0x1b5e0, 0x1b618, 0x1b660, 0x1b67c, 0x1b6c0, 0x1b738,
  0x1b782, 0x1b784, 0x1b788, 0x1b790, 0x1b79e, 0x1b7a0, 0x1b7cc,
  0x1b82e, 0x1b84e, 0x1b85c, 0x1b88e, 0x1b89c, 0x1b8b8, 0x1b8c2,
  0x1b8c4, 0x1b8c8, 0x1b8d0, 0x1b8e6, 0x1b8fa, 0x1b90e, 0x1b91c,
  0x1b938, 0x1b970, 0x1b97e, 0x1b982, 0x1b984, 0x1b988, 0x1b990,
  0x1b99e, 0x1b9a0, 0x1b9cc, 0x1b9f2, 0x1b9f4, 0x1ba0e, 0x1ba1c,
  0x1ba38, 0x1ba70, 0x1ba7e, 0x1bae0, 0x1bafc, 0x1bb08, 0x1bb10,
  0x1bb20, 0x1bb3c, 0x1bb40, 0x1bb98, 0x1bbce, 0x1bbe2, 0x1bbe4,
  0x1bbe8, 0x1bc16, 0x1bc26, 0x1bc2c, 0x1bc46, 0x1bc4c, 0x1bc58,
  0x1bc72, 0x1bc74, 0x1bc86, 0x1bc8c, 0x1bc98, 0x1bcb0, 0x1bcbe,
  0x1bcce, 0x1bce2, 0x1bce4, 0x1bce8, 0x1bd06, 0x1bd0c, 0x1bd18,
  0x1bd30, 0x1bd3e, 0x1bd60, 0x1bd7c, 0x1bd9c, 0x1bdc2, 0x1bdc4,
  0x1bdc8, 0x1bdd0, 0x1bde6, 0x1bdfa, 0x1be12, 0x1be14, 0x1be22,
  0x1be24, 0x1be28, 0x1be42, 0x1be44, 0x1be48, 0x1be50, 0x1be5e,
  0x1be66, 0x1be82, 0x1be84, 0x1be88, 0x1be90, 0x1be9e, 0x1bea0,
  0x1bebc, 0x1becc, 0x1bef4, 0x1bf1a, 0x1bf2e, 0x1bf32, 0x1bf34,
  0x1bf4e, 0x1bf5c, 0x1bf62, 0x1bf64, 0x1bf68, 0x1c09a, 0x1c0b2,
  0x1c0b4, 0x1c11a, 0x1c132, 0x1c134, 0x1c162, 0x1c164, 0x1c168,
  0x1c176, 0x1c1ba, 0x1c21a, 0x1c232, 0x1c234, 0x1c24e, 0x1c25c,
  0x1c262, 0x1c264, 0x1c268, 0x1c276, 0x1c28e, 0x1c2c2, 0x1c2c4,
  0x1c2c8, 0x1c2d0, 0x1c2de, 0x1c2e6, 0x1c2ec, 0x1c2fa, 0x1c316,
  0x1c326, 0x1c33a, 0x1c346, 0x1c34c, 0x1c372, 0x1c374, 0x1c41a,
  0x1c42e, 0x1c432, 0x1c434, 0x1c44e, 0x1c45c, 0x1c462, 0x1c464,
  0x1c468, 0x1c476, 0x1c48e, 0x1c49c, 0x1c4b8, 0x1c4c2, 0x1c4c8,
  0x1c4d0, 0x1c4de, 0x1c4e6, 0x1c4ec, 0x1c4fa, 0x1c51c, 0x1c538,
  0x1c570, 0x1c57e, 0x1c582, 0x1c584, 0x1c588, 0x1c590, 0x1c59e,
  0x1c5a0, 0x1c5bc, 0x1c5c6, 0x1c5cc, 0x1c5d8, 0x1c5ee, 0x1c5f2,
  0x1c5f4, 0x1c616, 0x1c626, 0x1c62c, 0x1c63a, 0x1c646, 0x1c64c,
  0x1c658, 0x1c66e, 0x1c672, 0x1c674, 0x1c686, 0x1c68c, 0x1c698,
  0x1c6b0, 0x1c6be, 0x1c6ce, 0x1c6dc, 0x1c6e2, 0x1c6e4, 0x1c6e8,
  0x1c712, 0x1c714, 0x1c722, 0x1c728, 0x1c736, 0x1c742, 0x1c744,
  0x1c748, 0x1c750, 0x1c75e, 0x1c766, 0x1c76c, 0x1c77a, 0x1c7ae,
  0x1c7d6, 0x1c7ea, 0x1c81a, 0x1c82e, 0x1c832, 0x1c834, 0x1c84e,
  0x1c85c, 0x1c862, 0x1c864, 0x1c868, 0x1c876, 0x1c88e, 0x1c89c,
  0x1c8b8, 0x1c8c2, 0x1c8c8, 0x1c8d0, 0x1c8de, 0x1c8e6, 0x1c8ec,
  0x1c8fa, 0x1c90e, 0x1c938, 0x1c970, 0x1c97e, 0x1c982, 0x1c984,
  0x1c990, 0x1c99e, 0x1c9a0, 0x1c9bc, 0x1c9c6, 0x1c9cc, 0x1c9d8,
  0x1c9ee, 0x1c9f2, 0x1c9f4, 0x1ca38, 0x1ca70, 0x1ca7e, 0x1cae0,
  0x1cafc, 0x1cb02, 0x1cb04, 0x1cb08, 0x1cb10, 0x1cb20, 0x1cb3c,
  0x1cb40, 0x1cb78, 0x1cb86, 0x1cb8c, 0x1cb98, 0x1cbb0, 0x1cbbe,
  0x1cbce, 0x1cbdc, 0x1cbe2, 0x1cbe4, 0x1cbe8, 0x1cbf6, 0x1cc16,
  0x1cc26, 0x1cc2c, 0x1cc3a, 0x1cc46, 0x1cc58, 0x1cc72, 0x1cc74,
  0x1cc86, 0x1ccb0, 0x1ccbe, 0x1ccce, 0x1cce2, 0x1cce4, 0x1cce8,
  0x1cd06, 0x1cd0c, 0x1cd18, 0x1cd30, 0x1cd3e, 0x1cd60, 0x1cd7c,
  0x1cd9c, 0x1cdc2, 0x1cdc4, 0x1cdc8, 0x1cdd0, 0x1cdde, 0x1cde6,
  0x1cdfa, 0x1ce22, 0x1ce28, 0x1ce42, 0x1ce50, 0x1ce5e, 0x1ce66,
  0x1ce7a, 0x1ce82, 0x1ce84, 0x1ce88, 0x1ce90, 0x1ce9e, 0x1cea0,
  0x1cebc, 0x1cecc, 0x1cef2, 0x1cef4, 0x1cf2e, 0x1cf32, 0x1cf34,
  0x1cf4e, 0x1cf5c, 0x1cf62, 0x1cf64, 0x1cf68, 0x1cf96, 0x1cfa6,
  0x1cfac, 0x1cfca, 0x1cfd2, 0x1cfd4, 0x1d02e, 0x1d032, 0x1d034,
  0x1d04e, 0x1d05c, 0x1d062, 0x1d064, 0x1d068, 0x1d076, 0x1d08e,
  0x1d09c, 0x1d0b8, 0x1d0c2, 0x1d0c4, 0x1d0c8, 0x1d0d0, 0x1d0de,
  0x1d0e6, 0x1d0ec, 0x1d0fa, 0x1d11c, 0x1d138, 0x1d170, 0x1d17e,
  0x1d182, 0x1d184, 0x1d188, 0x1d190, 0x1d19e, 0x1d1a0, 0x1d1bc,
  0x1d1c6, 0x1d1cc, 0x1d1d8, 0x1d1ee, 0x1d1f2, 0x1d1f4, 0x1d21c,
  0x1d238, 0x1d270, 0x1d27e, 0x1d2e0, 0x1d2fc, 0x1d302, 0x1d304,
  0x1d308, 0x1d310, 0x1d31e, 0x1d320, 0x1d33c, 0x1d340, 0x1d378,
  0x1d386, 0x1d38c, 0x1d398, 0x1d3b0, 0x1d3be, 0x1d3ce, 0x1d3dc,
  0x1d3e2, 0x1d3e4, 0x1d3e8, 0x1d3f6, 0x1d470, 0x1d47e, 0x1d4e0,
  0x1d4fc, 0x1d5c0, 0x1d5f8, 0x1d604, 0x1d608, 0x1d610, 0x1d620,
  0x1d640, 0x1d678, 0x1d6f0, 0x1d706, 0x1d70c, 0x1d718, 0x1d730,
  0x1d73e, 0x1d760, 0x1d77c, 0x1d78e, 0x1d79c, 0x1d7b8, 0x1d7c2,
  0x1d7c4, 0x1d7c8, 0x1d7d0, 0x1d7de, 0x1d7e6, 0x1d7ec, 0x1d826,
  0x1d82c, 0x1d83a, 0x1d846, 0x1d84c, 0x1d858, 0x1d872, 0x1d874,
  0x1d886, 0x1d88c, 0x1d898, 0x1d8b0, 0x1d8be, 0x1d8ce, 0x1d8e2,
  0x1d8e4, 0x1d8e8, 0x1d8f6, 0x1d90c, 0x1d918, 0x1d930, 0x1d93e,
  0x1d960, 0x1d97c, 0x1d99c, 0x1d9c2, 0x1d9c4, 0x1d9c8, 0x1d9d0,
  0x1d9e6, 0x1d9fa, 0x1da0c, 0x1da18, 0x1da30, 0x1da3e, 0x1da60,
  0x1da7c, 0x1dac0, 0x1daf8, 0x1db38, 0x1db82, 0x1db84, 0x1db88,
  0x1db90, 0x1db9e, 0x1dba0, 0x1dbcc, 0x1dbf2, 0x1dbf4, 0x1dc22,
  0x1dc42, 0x1dc44, 0x1dc48, 0x1dc50, 0x1dc5e, 0x1dc66, 0x1dc7a,
  0x1dc82, 0x1dc84, 0x1dc88, 0x1dc90, 0x1dc9e, 0x1dca0, 0x1dcbc,
  0x1dccc, 0x1dcf2, 0x1dcf4, 0x1dd04, 0x1dd08, 0x1dd10, 0x1dd1e,
  0x1dd20, 0x1dd3c, 0x1dd40, 0x1dd78, 0x1dd86, 0x1dd98, 0x1ddce,
  0x1dde2, 0x1dde4, 0x1dde8, 0x1de2e, 0x1de32, 0x1de34, 0x1de4e,
  0x1de5c, 0x1de62, 0x1de64, 0x1de68, 0x1de8e, 0x1de9c, 0x1deb8,
  0x1dec2, 0x1dec4, 0x1dec8, 0x1ded0, 0x1dee6, 0x1defa, 0x1df16,
  0x1df26, 0x1df2c, 0x1df46, 0x1df4c, 0x1df58, 0x1df72, 0x1df74,
  0x1df8a, 0x1df92, 0x1df94, 0x1dfa2, 0x1dfa4, 0x1dfa8, 0x1e08a,
  0x1e092, 0x1e094, 0x1e0a2, 0x1e0a4, 0x1e0a8, 0x1e0b6, 0x1e0da,
  0x1e10a, 0x1e112, 0x1e114, 0x1e122, 0x1e124, 0x1e128, 0x1e136,
  0x1e142, 0x1e144, 0x1e148, 0x1e150, 0x1e166, 0x1e16c, 0x1e17a,
  0x1e19a, 0x1e1b2, 0x1e1b4, 0x1e20a, 0x1e212, 0x1e214, 0x1e222,
  0x1e224, 0x1e228, 0x1e236, 0x1e242, 0x1e248, 0x1e250, 0x1e25e,
  0x1e266, 0x1e26c, 0x1e27a, 0x1e282, 0x1e284, 0x1e288, 0x1e290,
  0x1e2a0, 0x1e2bc, 0x1e2c6, 0x1e2cc, 0x1e2d8, 0x1e2ee, 0x1e2f2,
  0x1e2f4, 0x1e31a, 0x1e332, 0x1e334, 0x1e35c, 0x1e362, 0x1e364,
  0x1e368, 0x1e3ba, 0x1e40a, 0x1e412, 0x1e414, 0x1e422, 0x1e428,
  0x1e436, 0x1e442, 0x1e448, 0x1e450, 0x1e45e, 0x1e466, 0x1e46c,
  0x1e47a, 0x1e482, 0x1e484, 0x1e490, 0x1e49e, 0x1e4a0, 0x1e4bc,
  0x1e4c6, 0x1e4cc, 0x1e4d8, 0x1e4ee, 0x1e4f2, 0x1e4f4, 0x1e502,
  0x1e504, 0x1e508, 0x1e510, 0x1e51e, 0x1e520, 0x1e53c, 0x1e540,
  0x1e578, 0x1e586, 0x1e58c, 0x1e598, 0x1e5b0, 0x1e5be, 0x1e5ce,
  0x1e5dc, 0x1e5e2, 0x1e5e4, 0x1e5e8, 0x1e5f6, 0x1e61a, 0x1e62e,
  0x1e632, 0x1e634, 0x1e64e, 0x1e65c, 0x1e662, 0x1e668, 0x1e68e,
  0x1e69c, 0x1e6b8, 0x1e6c2, 0x1e6c4, 0x1e6c8, 0x1e6d0, 0x1e6e6,
  0x1e6fa, 0x1e716, 0x1e726, 0x1e72c, 0x1e73a, 0x1e746, 0x1e74c,
  0x1e758, 0x1e772, 0x1e774, 0x1e792, 0x1e794, 0x1e7a2, 0x1e7a4,
  0x1e7a8, 0x1e7b6, 0x1e812, 0x1e814, 0x1e822, 0x1e824, 0x1e828,
  0x1e836, 0x1e842, 0x1e844, 0x1e848, 0x1e850, 0x1e85e, 0x1e866,
  0x1e86c, 0x1e87a, 0x1e882, 0x1e884, 0x1e888, 0x1e890, 0x1e89e,
  0x1e8a0, 0x1e8bc, 0x1e8c6, 0x1e8cc, 0x1e8d8, 0x1e8ee, 0x1e8f2,
  0x1e8f4, 0x1e902, 0x1e904, 0x1e908, 0x1e910, 0x1e920, 0x1e93c,
  0x1e940, 0x1e978, 0x1e986, 0x1e98c, 0x1e998, 0x1e9b0, 0x1e9be,
  0x1e9ce, 0x1e9dc, 0x1e9e2, 0x1e9e4, 0x1e9e8, 0x1e9f6, 0x1ea04,
  0x1ea08, 0x1ea10, 0x1ea20, 0x1ea40, 0x1ea78, 0x1eaf0, 0x1eb06,
  0x1eb0c, 0x1eb18, 0x1eb30, 0x1eb3e, 0x1eb60, 0x1eb7c, 0x1eb8e,
  0x1eb9c, 0x1ebb8, 0x1ebc2, 0x1ebc4, 0x1ebc8, 0x1ebd0, 0x1ebde,
  0x1ebe6, 0x1ebec, 0x1ec1a, 0x1ec2e, 0x1ec32, 0x1ec34, 0x1ec4e,
  0x1ec5c, 0x1ec62, 0x1ec64, 0x1ec68, 0x1ec8e, 0x1ec9c, 0x1ecb8,
  0x1ecc2, 0x1ecc4, 0x1ecc8, 0x1ecd0, 0x1ece6, 0x1ecfa, 0x1ed0e,
  0x1ed1c, 0x1ed38, 0x1ed70, 0x1ed7e, 0x1ed82, 0x1ed84, 0x1ed88,
  0x1ed90, 0x1ed9e, 0x1eda0, 0x1edcc, 0x1edf2, 0x1edf4, 0x1ee16,
  0x1ee26, 0x1ee2c, 0x1ee3a, 0x1ee46, 0x1ee4c, 0x1ee58, 0x1ee6e,
  0x1ee72, 0x1ee74, 0x1ee86, 0x1ee8c, 0x1ee98, 0x1eeb0, 0x1eebe,
  0x1eece, 0x1eedc, 0x1eee2, 0x1eee4, 0x1eee8, 0x1ef12, 0x1ef22,
  0x1ef24, 0x1ef28, 0x1ef36, 0x1ef42, 0x1ef44, 0x1ef48, 0x1ef50,
  0x1ef5e, 0x1ef66, 0x1ef6c, 0x1ef7a, 0x1efae, 0x1efb2, 0x1efb4,
  0x1efd6, 0x1f096, 0x1f0a6, 0x1f0ac, 0x1f0ba, 0x1f0ca, 0x1f0d2,
  0x1f0d4, 0x1f116, 0x1f126, 0x1f12c, 0x1f13a, 0x1f146, 0x1f14c,
  0x1f158, 0x1f16e, 0x1f172, 0x1f174, 0x1f18a, 0x1f192, 0x1f194,
  0x1f1a2, 0x1f1a4, 0x1f1a8, 0x1f1da, 0x1f216, 0x1f226, 0x1f22c,
  0x1f23a, 0x1f246, 0x1f258, 0x1f26e, 0x1f272, 0x1f274, 0x1f286,
  0x1f28c, 0x1f298, 0x1f2b0, 0x1f2be, 0x1f2ce, 0x1f2dc, 0x1f2e2,
  0x1f2e4, 0x1f2e8, 0x1f2f6, 0x1f30a, 0x1f312, 0x1f314, 0x1f322,
  0x1f328, 0x1f342, 0x1f344, 0x1f348, 0x1f350, 0x1f35e, 0x1f366,
  0x1f37a, 0x1f39a, 0x1f3ae, 0x1f3b2, 0x1f3b4, 0x1f416, 0x1f426,
  0x1f42c, 0x1f43a, 0x1f446, 0x1f44c, 0x1f458, 0x1f46e, 0x1f472,
  0x1f474, 0x1f486, 0x1f48c, 0x1f498, 0x1f4b0, 0x1f4be, 0x1f4ce,
  0x1f4dc, 0x1f4e2, 0x1f4e4, 0x1f4e8, 0x1f4f6, 0x1f506, 0x1f50c,
  0x1f518, 0x1f530, 0x1f53e, 0x1f560, 0x1f57c, 0x1f58e, 0x1f59c,
  0x1f5b8, 0x1f5c2, 0x1f5c4, 0x1f5c8, 0x1f5d0, 0x1f5de, 0x1f5e6,
  0x1f5ec, 0x1f5fa, 0x1f60a, 0x1f612, 0x1f614, 0x1f622, 0x1f624,
  0x1f628, 0x1f636, 0x1f642, 0x1f644, 0x1f648, 0x1f650, 0x1f65e,
  0x1f666, 0x1f67a, 0x1f682, 0x1f684, 0x1f688, 0x1f690, 0x1f69e,
  0x1f6a0, 0x1f6bc, 0x1f6cc, 0x1f6f2, 0x1f6f4, 0x1f71a, 0x1f72e,
  0x1f732, 0x1f734, 0x1f74e, 0x1f75c, 0x1f762, 0x1f764, 0x1f768,
  0x1f776, 0x1f796, 0x1f7a6, 0x1f7ac, 0x1f7ba, 0x1f7d2, 0x1f7d4,
  0x1f89a, 0x1f8ae, 0x1f8b2, 0x1f8b4, 0x1f8d6, 0x1f8ea, 0x1f91a,
  0x1f92e, 0x1f932, 0x1f934, 0x1f94e, 0x1f95c, 0x1f962, 0x1f964,
  0x1f968, 0x1f976, 0x1f996, 0x1f9a6, 0x1f9ac, 0x1f9ba, 0x1f9ca,
  0x1f9d2, 0x1f9d4, 0x1fa1a, 0x1fa2e, 0x1fa32, 0x1fa34, 0x1fa4e,
  0x1fa5c, 0x1fa62, 0x1fa64, 0x1fa68, 0x1fa76, 0x1fa8e, 0x1fa9c,
  0x1fab8, 0x1fac2, 0x1fac4, 0x1fac8, 0x1fad0, 0x1fade, 0x1fae6,
  0x1faec, 0x1fb16, 0x1fb26, 0x1fb2c, 0x1fb3a, 0x1fb46, 0x1fb4c,
  0x1fb58, 0x1fb6e, 0x1fb72, 0x1fb74, 0x1fb8a, 0x1fb92, 0x1fb94,
  0x1fba2, 0x1fba4, 0x1fba8, 0x1fbb6, 0x1fbda
};

const int BitMatrixParser::CODEWORD_TABLE[] =
{
  2627, 1819, 2622, 2621, 1813, 1812, 2729, 2724, 2723,
  2779, 2774, 2773,  902,  896,  908,  868,  865,  861,
  859, 2511,  873,  871, 1780,  835, 2493,  825, 2491,
  842,  837,  844, 1764, 1762,  811,  810,  809, 2483,
  807, 2482,  806, 2480,  815,  814,  813,  812, 2484,
  817,  816, 1745, 1744, 1742, 1746, 2655, 2637, 2635,
  2626, 2625, 2623, 2628, 1820, 2752, 2739, 2737, 2728,
  2727, 2725, 2730, 2785, 2783, 2778, 2777, 2775, 2780,
  787,  781,  747,  739,  736, 2413,  754,  752, 1719,
  692,  689,  681, 2371,  678, 2369,  700,  697,  694,
  703, 1688, 1686,  642,  638, 2343,  631, 2341,  627,
  2338,  651,  646,  643, 2345,  654,  652, 1652, 1650,
  1647, 1654,  601,  599, 2322,  596, 2321,  594, 2319,
  2317,  611,  610,  608,  606, 2324,  603, 2323,  615,
  614,  612, 1617, 1616, 1614, 1612,  616, 1619, 1618,
  2575, 2538, 2536,  905,  901,  898,  909, 2509, 2507,
  2504,  870,  867,  864,  860, 2512,  875,  872, 1781,
  2490, 2489, 2487, 2485, 1748,  836,  834,  832,  830,
  2494,  827, 2492,  843,  841,  839,  845, 1765, 1763,
  2701, 2676, 2674, 2653, 2648, 2656, 2634, 2633, 2631,
  2629, 1821, 2638, 2636, 2770, 2763, 2761, 2750, 2745,
  2753, 2736, 2735, 2733, 2731, 1848, 2740, 2738, 2786,
  2784,  591,  588,  576,  569,  566, 2296, 1590,  537,
  534,  526, 2276,  522, 2274,  545,  542,  539,  548,
  1572, 1570,  481, 2245,  466, 2242,  462, 2239,  492,
  485,  482, 2249,  496,  494, 1534, 1531, 1528, 1538,
  413, 2196,  406, 2191, 2188,  425,  419, 2202,  415,
  2199,  432,  430,  427, 1472, 1467, 1464,  433, 1476,
  1474,  368,  367, 2160,  365, 2159,  362, 2157, 2155,
  2152,  378,  377,  375, 2166,  372, 2165,  369, 2162,
  383,  381,  379, 2168, 1419, 1418, 1416, 1414,  385,
  1411,  384, 1423, 1422, 1420, 1424, 2461,  802, 2441,
  2439,  790,  786,  783,  794, 2409, 2406, 2403,  750,
  742,  738, 2414,  756,  753, 1720, 2367, 2365, 2362,
  2359, 1663,  693,  691,  684, 2373,  680, 2370,  702,
  699,  696,  704, 1690, 1687, 2337, 2336, 2334, 2332,
  1624, 2329, 1622,  640,  637, 2344,  634, 2342,  630,
  2340,  650,  648,  645, 2346,  655,  653, 1653, 1651,
  1649, 1655, 2612, 2597, 2595, 2571, 2568, 2565, 2576,
  2534, 2529, 2526, 1787, 2540, 2537,  907,  904,  900,
  910, 2503, 2502, 2500, 2498, 1768, 2495, 1767, 2510,
  2508, 2506,  869,  866,  863, 2513,  876,  874, 1782,
  2720, 2713, 2711, 2697, 2694, 2691, 2702, 2672, 2670,
  2664, 1828, 2678, 2675, 2647, 2646, 2644, 2642, 1823,
  2639, 1822, 2654, 2652, 2650, 2657, 2771, 1855, 2765,
  2762, 1850, 1849, 2751, 2749, 2747, 2754,  353, 2148,
  344,  342,  336, 2142,  332, 2140,  345, 1375, 1373,
  306, 2130,  299, 2128,  295, 2125,  319,  314,  311,
  2132, 1354, 1352, 1349, 1356,  262,  257, 2101,  253,
  2096, 2093,  274,  273,  267, 2107,  263, 2104,  280,
  278,  275, 1316, 1311, 1308, 1320, 1318, 2052,  202,
  2050, 2044, 2040,  219, 2063,  212, 2060,  208, 2055,
  224,  221, 2066, 1260, 1258, 1252,  231, 1248,  229,
  1266, 1264, 1261, 1268,  155, 1998,  153, 1996, 1994,
  1991, 1988,  165,  164, 2007,  162, 2006,  159, 2003,
  2000,  172,  171,  169, 2012,  166, 2010, 1186, 1184,
  1182, 1179,  175, 1176,  173, 1192, 1191, 1189, 1187,
  176, 1194, 1193, 2313, 2307, 2305,  592,  589, 2294,
  2292, 2289,  578,  572,  568, 2297,  580, 1591, 2272,
  2267, 2264, 1547,  538,  536,  529, 2278,  525, 2275,
  547,  544,  541, 1574, 1571, 2237, 2235, 2229, 1493,
  2225, 1489,  478, 2247,  470, 2244,  465, 2241,  493,
  488,  484, 2250,  498,  495, 1536, 1533, 1530, 1539,
  2187, 2186, 2184, 2182, 1432, 2179, 1430, 2176, 1427,
  414,  412, 2197,  409, 2195,  405, 2193, 2190,  426,
  424,  421, 2203,  418, 2201,  431,  429, 1473, 1471,
  1469, 1466,  434, 1477, 1475, 2478, 2472, 2470, 2459,
  2457, 2454, 2462,  803, 2437, 2432, 2429, 1726, 2443,
  2440,  792,  789,  785, 2401, 2399, 2393, 1702, 2389,
  1699, 2411, 2408, 2405,  745,  741, 2415,  758,  755,
  1721, 2358, 2357, 2355, 2353, 1661, 2350, 1660, 2347,
  1657, 2368, 2366, 2364, 2361, 1666,  690,  687, 2374,
  683, 2372,  701,  698,  705, 1691, 1689, 2619, 2617,
  2610, 2608, 2605, 2613, 2593, 2588, 2585, 1803, 2599,
  2596, 2563, 2561, 2555, 1797, 2551, 1795, 2573, 2570,
  2567, 2577, 2525, 2524, 2522, 2520, 1786, 2517, 1785,
  2514, 1783, 2535, 2533, 2531, 2528, 1788, 2541, 2539,
  906,  903,  911, 2721, 1844, 2715, 2712, 1838, 1836,
  2699, 2696, 2693, 2703, 1827, 1826, 1824, 2673, 2671,
  2669, 2666, 1829, 2679, 2677, 1858, 1857, 2772, 1854,
  1853, 1851, 1856, 2766, 2764,  143, 1987,  139, 1986,
  135,  133,  131, 1984,  128, 1983,  125, 1981,  138,
  137,  136, 1985, 1133, 1132, 1130,  112,  110, 1974,
  107, 1973,  104, 1971, 1969,  122,  121,  119,  117,
  1977,  114, 1976,  124, 1115, 1114, 1112, 1110, 1117,
  1116,   84,   83, 1953,   81, 1952,   78, 1950, 1948,
  1945,   94,   93,   91, 1959,   88, 1958,   85, 1955,
  99,   97,   95, 1961, 1086, 1085, 1083, 1081, 1078,
  100, 1090, 1089, 1087, 1091,   49,   47, 1917,   44,
  1915, 1913, 1910, 1907,   59, 1926,   56, 1925,   53,
  1922, 1919,   66,   64, 1931,   61, 1929, 1042, 1040,
  1038,   71, 1035,   70, 1032,   68, 1048, 1047, 1045,
  1043, 1050, 1049,   12,   10, 1869, 1867, 1864, 1861,
  21, 1880,   19, 1877, 1874, 1871,   28, 1888,   25,
  1886,   22, 1883,  982,  980,  977,  974,   32,   30,
  991,  989,  987,  984,   34,  995,  994,  992, 2151,
  2150, 2147, 2146, 2144,  356,  355,  354, 2149, 2139,
  2138, 2136, 2134, 1359,  343,  341,  338, 2143,  335,
  2141,  348,  347,  346, 1376, 1374, 2124, 2123, 2121,
  2119, 1326, 2116, 1324,  310,  308,  305, 2131,  302,
  2129,  298, 2127,  320,  318,  316,  313, 2133,  322,
  321, 1355, 1353, 1351, 1357, 2092, 2091, 2089, 2087,
  1276, 2084, 1274, 2081, 1271,  259, 2102,  256, 2100,
  252, 2098, 2095,  272,  269, 2108,  266, 2106,  281,
  279,  277, 1317, 1315, 1313, 1310,  282, 1321, 1319,
  2039, 2037, 2035, 2032, 1203, 2029, 1200, 1197,  207,
  2053,  205, 2051,  201, 2049, 2046, 2043,  220,  218,
  2064,  215, 2062,  211, 2059,  228,  226,  223, 2069,
  1259, 1257, 1254,  232, 1251,  230, 1267, 1265, 1263,
  2316, 2315, 2312, 2311, 2309, 2314, 2304, 2303, 2301,
  2299, 1593, 2308, 2306,  590, 2288, 2287, 2285, 2283,
  1578, 2280, 1577, 2295, 2293, 2291,  579,  577,  574,
  571, 2298,  582,  581, 1592, 2263, 2262, 2260, 2258,
  1545, 2255, 1544, 2252, 1541, 2273, 2271, 2269, 2266,
  1550,  535,  532, 2279,  528, 2277,  546,  543,  549,
  1575, 1573, 2224, 2222, 2220, 1486, 2217, 1485, 2214,
  1482, 1479, 2238, 2236, 2234, 2231, 1496, 2228, 1492,
  480,  477, 2248,  473, 2246,  469, 2243,  490,  487,
  2251,  497, 1537, 1535, 1532, 2477, 2476, 2474, 2479,
  2469, 2468, 2466, 2464, 1730, 2473, 2471, 2453, 2452,
  2450, 2448, 1729, 2445, 1728, 2460, 2458, 2456, 2463,
  805,  804, 2428, 2427, 2425, 2423, 1725, 2420, 1724,
  2417, 1722, 2438, 2436, 2434, 2431, 1727, 2444, 2442,
  793,  791,  788,  795, 2388, 2386, 2384, 1697, 2381,
  1696, 2378, 1694, 1692, 2402, 2400, 2398, 2395, 1703,
  2392, 1701, 2412, 2410, 2407,  751,  748,  744, 2416,
  759,  757, 1807, 2620, 2618, 1806, 1805, 2611, 2609,
  2607, 2614, 1802, 1801, 1799, 2594, 2592, 2590, 2587,
  1804, 2600, 2598, 1794, 1793, 1791, 1789, 2564, 2562,
  2560, 2557, 1798, 2554, 1796, 2574, 2572, 2569, 2578,
  1847, 1846, 2722, 1843, 1842, 1840, 1845, 2716, 2714,
  1835, 1834, 1832, 1830, 1839, 1837, 2700, 2698, 2695,
  2704, 1817, 1811, 1810,  897,  862, 1777,  829,  826,
  838, 1760, 1758,  808, 2481, 1741, 1740, 1738, 1743,
  2624, 1818, 2726, 2776,  782,  740,  737, 1715,  686,
  679,  695, 1682, 1680,  639,  628, 2339,  647,  644,
  1645, 1643, 1640, 1648,  602,  600,  597,  595, 2320,
  593, 2318,  609,  607,  604, 1611, 1610, 1608, 1606,
  613, 1615, 1613, 2328,  926,  924,  892,  886,  899,
  857,  850, 2505, 1778,  824,  823,  821,  819, 2488,
  818, 2486,  833,  831,  828,  840, 1761, 1759, 2649,
  2632, 2630, 2746, 2734, 2732, 2782, 2781,  570,  567,
  1587,  531,  527,  523,  540, 1566, 1564,  476,  467,
  463, 2240,  486,  483, 1524, 1521, 1518, 1529,  411,
  403, 2192,  399, 2189,  423,  416, 1462, 1457, 1454,
  428, 1468, 1465, 2210,  366,  363, 2158,  360, 2156,
  357, 2153,  376,  373,  370, 2163, 1410, 1409, 1407,
  1405,  382, 1402,  380, 1417, 1415, 1412, 1421, 2175,
  2174,  777,  774,  771,  784,  732,  725,  722, 2404,
  743, 1716,  676,  674,  668, 2363,  665, 2360,  685,
  1684, 1681,  626,  624,  622, 2335,  620, 2333,  617,
  2330,  641,  635,  649, 1646, 1644, 1642, 2566,  928,
  925, 2530, 2527,  894,  891,  888, 2501, 2499, 2496,
  858,  856,  854,  851, 1779, 2692, 2668, 2665, 2645,
  2643, 2640, 2651, 2768, 2759, 2757, 2744, 2743, 2741,
  2748,  352, 1382,  340,  337,  333, 1371, 1369,  307,
  300,  296, 2126,  315,  312, 1347, 1342, 1350,  261,
  258,  250, 2097,  246, 2094,  271,  268,  264, 1306,
  1301, 1298,  276, 1312, 1309, 2115,  203, 2048,  195,
  2045,  191, 2041,  213,  209, 2056, 1246, 1244, 1238,
  225, 1234,  222, 1256, 1253, 1249, 1262, 2080, 2079,
  154, 1997,  150, 1995,  147, 1992, 1989,  163,  160,
  2004,  156, 2001, 1175, 1174, 1172, 1170, 1167,  170,
  1164,  167, 1185, 1183, 1180, 1177,  174, 1190, 1188,
  2025, 2024, 2022,  587,  586,  564,  559,  556, 2290,
  573, 1588,  520,  518,  512, 2268,  508, 2265,  530,
  1568, 1565,  461,  457, 2233,  450, 2230,  446, 2226,
  479,  471,  489, 1526, 1523, 1520,  397,  395, 2185,
  392, 2183,  389, 2180, 2177,  410, 2194,  402,  422,
  1463, 1461, 1459, 1456, 1470, 2455,  799, 2433, 2430,
  779,  776,  773, 2397, 2394, 2390,  734,  728,  724,
  746, 1717, 2356, 2354, 2351, 2348, 1658,  677,  675,
  673,  670,  667,  688, 1685, 1683, 2606, 2589, 2586,
  2559, 2556, 2552,  927, 2523, 2521, 2518, 2515, 1784,
  2532,  895,  893,  890, 2718, 2709, 2707, 2689, 2687,
  2684, 2663, 2662, 2660, 2658, 1825, 2667, 2769, 1852,
  2760, 2758,  142,  141, 1139, 1138,  134,  132,  129,
  126, 1982, 1129, 1128, 1126, 1131,  113,  111,  108,
  105, 1972,  101, 1970,  120,  118,  115, 1109, 1108,
  1106, 1104,  123, 1113, 1111,   82,   79, 1951,   75,
  1949,   72, 1946,   92,   89,   86, 1956, 1077, 1076,
  1074, 1072,   98, 1069,   96, 1084, 1082, 1079, 1088,
  1968, 1967,   48,   45, 1916,   42, 1914,   39, 1911,
  1908,   60,   57,   54, 1923,   50, 1920, 1031, 1030,
  1028, 1026,   67, 1023,   65, 1020,   62, 1041, 1039,
  1036, 1033,   69, 1046, 1044, 1944, 1943, 1941,   11,
  9, 1868,    7, 1865, 1862, 1859,   20, 1878,   16,
  1875,   13, 1872,  970,  968,  966,  963,   29,  960,
  26,   23,  983,  981,  978,  975,   33,  971,   31,
  990,  988,  985, 1906, 1904, 1902,  993,  351, 2145,
  1383,  331,  330,  328,  326, 2137,  323, 2135,  339,
  1372, 1370,  294,  293,  291,  289, 2122,  286, 2120,
  283, 2117,  309,  303,  317, 1348, 1346, 1344,  245,
  244,  242, 2090,  239, 2088,  236, 2085, 2082,  260,
  2099,  249,  270, 1307, 1305, 1303, 1300, 1314,  189,
  2038,  186, 2036,  183, 2033, 2030, 2026,  206,  198,
  2047,  194,  216, 1247, 1245, 1243, 1240,  227, 1237,
  1255, 2310, 2302, 2300, 2286, 2284, 2281,  565,  563,
  561,  558,  575, 1589, 2261, 2259, 2256, 2253, 1542,
  521,  519,  517,  514, 2270,  511,  533, 1569, 1567,
  2223, 2221, 2218, 2215, 1483, 2211, 1480,  459,  456,
  453, 2232,  449,  474,  491, 1527, 1525, 1522, 2475,
  2467, 2465, 2451, 2449, 2446,  801,  800, 2426, 2424,
  2421, 2418, 1723, 2435,  780,  778,  775, 2387, 2385,
  2382, 2379, 1695, 2375, 1693, 2396,  735,  733,  730,
  727,  749, 1718, 2616, 2615, 2604, 2603, 2601, 2584,
  2583, 2581, 2579, 1800, 2591, 2550, 2549, 2547, 2545,
  1792, 2542, 1790, 2558,  929, 2719, 1841, 2710, 2708,
  1833, 1831, 2690, 2688, 2686, 1815, 1809, 1808, 1774,
  1756, 1754, 1737, 1736, 1734, 1739, 1816, 1711, 1676,
  1674,  633,  629, 1638, 1636, 1633, 1641,  598, 1605,
  1604, 1602, 1600,  605, 1609, 1607, 2327,  887,  853,
  1775,  822,  820, 1757, 1755, 1584,  524, 1560, 1558,
  468,  464, 1514, 1511, 1508, 1519,  408,  404,  400,
  1452, 1447, 1444,  417, 1458, 1455, 2208,  364,  361,
  358, 2154, 1401, 1400, 1398, 1396,  374, 1393,  371,
  1408, 1406, 1403, 1413, 2173, 2172,  772,  726,  723,
  1712,  672,  669,  666,  682, 1678, 1675,  625,  623,
  621,  618, 2331,  636,  632, 1639, 1637, 1635,  920,
  918,  884,  880,  889,  849,  848,  847,  846, 2497,
  855,  852, 1776, 2641, 2742, 2787, 1380,  334, 1367,
  1365,  301,  297, 1340, 1338, 1335, 1343,  255,  251,
  247, 1296, 1291, 1288,  265, 1302, 1299, 2113,  204,
  196,  192, 2042, 1232, 1230, 1224,  214, 1220,  210,
  1242, 1239, 1235, 1250, 2077, 2075,  151,  148, 1993,
  144, 1990, 1163, 1162, 1160, 1158, 1155,  161, 1152,
  157, 1173, 1171, 1168, 1165,  168, 1181, 1178, 2021,
  2020, 2018, 2023,  585,  560,  557, 1585,  516,  509,
  1562, 1559,  458,  447, 2227,  472, 1516, 1513, 1510,
  398,  396,  393,  390, 2181,  386, 2178,  407, 1453,
  1451, 1449, 1446,  420, 1460, 2209,  769,  764,  720,
  712, 2391,  729, 1713,  664,  663,  661,  659, 2352,
  656, 2349,  671, 1679, 1677, 2553,  922,  919, 2519,
  2516,  885,  883,  881, 2685, 2661, 2659, 2767, 2756,
  2755,  140, 1137, 1136,  130,  127, 1125, 1124, 1122,
  1127,  109,  106,  102, 1103, 1102, 1100, 1098,  116,
  1107, 1105, 1980,   80,   76,   73, 1947, 1068, 1067,
  1065, 1063,   90, 1060,   87, 1075, 1073, 1070, 1080,
  1966, 1965,   46,   43,   40, 1912,   36, 1909, 1019,
  1018, 1016, 1014,   58, 1011,   55, 1008,   51, 1029,
  1027, 1024, 1021,   63, 1037, 1034, 1940, 1939, 1937,
  1942,    8, 1866,    4, 1863,    1, 1860,  956,  954,
  952,  949,  946,   17,   14,  969,  967,  964,  961,
  27,  957,   24,  979,  976,  972, 1901, 1900, 1898,
  1896,  986, 1905, 1903,  350,  349, 1381,  329,  327,
  324, 1368, 1366,  292,  290,  287,  284, 2118,  304,
  1341, 1339, 1337, 1345,  243,  240,  237, 2086,  233,
  2083,  254, 1297, 1295, 1293, 1290, 1304, 2114,  190,
  187,  184, 2034,  180, 2031,  177, 2027,  199, 1233,
  1231, 1229, 1226,  217, 1223, 1241, 2078, 2076,  584,
  555,  554,  552,  550, 2282,  562, 1586,  507,  506,
  504,  502, 2257,  499, 2254,  515, 1563, 1561,  445,
  443,  441, 2219,  438, 2216,  435, 2212,  460,  454,
  475, 1517, 1515, 1512, 2447,  798,  797, 2422, 2419,
  770,  768,  766, 2383, 2380, 2376,  721,  719,  717,
  714,  731, 1714, 2602, 2582, 2580, 2548, 2546, 2543,
  923,  921, 2717, 2706, 2705, 2683, 2682, 2680, 1771,
  1752, 1750, 1733, 1732, 1731, 1735, 1814, 1707, 1670,
  1668, 1631, 1629, 1626, 1634, 1599, 1598, 1596, 1594,
  1603, 1601, 2326, 1772, 1753, 1751, 1581, 1554, 1552,
  1504, 1501, 1498, 1509, 1442, 1437, 1434,  401, 1448,
  1445, 2206, 1392, 1391, 1389, 1387, 1384,  359, 1399,
  1397, 1394, 1404, 2171, 2170, 1708, 1672, 1669,  619,
  1632, 1630, 1628, 1773, 1378, 1363, 1361, 1333, 1328,
  1336, 1286, 1281, 1278,  248, 1292, 1289, 2111, 1218,
  1216, 1210,  197, 1206,  193, 1228, 1225, 1221, 1236,
  2073, 2071, 1151, 1150, 1148, 1146,  152, 1143,  149,
  1140,  145, 1161, 1159, 1156, 1153,  158, 1169, 1166,
  2017, 2016, 2014, 2019, 1582,  510, 1556, 1553,  452,
  448, 1506, 1500,  394,  391,  387, 1443, 1441, 1439,
  1436, 1450, 2207,  765,  716,  713, 1709,  662,  660,
  657, 1673, 1671,  916,  914,  879,  878,  877,  882,
  1135, 1134, 1121, 1120, 1118, 1123, 1097, 1096, 1094,
  1092,  103, 1101, 1099, 1979, 1059, 1058, 1056, 1054,
  77, 1051,   74, 1066, 1064, 1061, 1071, 1964, 1963,
  1007, 1006, 1004, 1002,  999,   41,  996,   37, 1017,
  1015, 1012, 1009,   52, 1025, 1022, 1936, 1935, 1933,
  1938,  942,  940,  938,  935,  932,    5,    2,  955,
  953,  950,  947,   18,  943,   15,  965,  962,  958,
  1895, 1894, 1892, 1890,  973, 1899, 1897, 1379,  325,
  1364, 1362,  288,  285, 1334, 1332, 1330,  241,  238,
  234, 1287, 1285, 1283, 1280, 1294, 2112,  188,  185,
  181,  178, 2028, 1219, 1217, 1215, 1212,  200, 1209,
  1227, 2074, 2072,  583,  553,  551, 1583,  505,  503,
  500,  513, 1557, 1555,  444,  442,  439,  436, 2213,
  455,  451, 1507, 1505, 1502,  796,  763,  762,  760,
  767,  711,  710,  708,  706, 2377,  718,  715, 1710,
  2544,  917,  915, 2681, 1627, 1597, 1595, 2325, 1769,
  1749, 1747, 1499, 1438, 1435, 2204, 1390, 1388, 1385,
  1395, 2169, 2167, 1704, 1665, 1662, 1625, 1623, 1620,
  1770, 1329, 1282, 1279, 2109, 1214, 1207, 1222, 2068,
  2065, 1149, 1147, 1144, 1141,  146, 1157, 1154, 2013,
  2011, 2008, 2015, 1579, 1549, 1546, 1495, 1487, 1433,
  1431, 1428, 1425,  388, 1440, 2205, 1705,  658, 1667,
  1664, 1119, 1095, 1093, 1978, 1057, 1055, 1052, 1062,
  1962, 1960, 1005, 1003, 1000,  997,   38, 1013, 1010,
  1932, 1930, 1927, 1934,  941,  939,  936,  933,    6,
  930,    3,  951,  948,  944, 1889, 1887, 1884, 1881,
  959, 1893, 1891,   35, 1377, 1360, 1358, 1327, 1325,
  1322, 1331, 1277, 1275, 1272, 1269,  235, 1284, 2110,
  1205, 1204, 1201, 1198,  182, 1195,  179, 1213, 2070,
  2067, 1580,  501, 1551, 1548,  440,  437, 1497, 1494,
  1490, 1503,  761,  709,  707, 1706,  913,  912, 2198,
  1386, 2164, 2161, 1621, 1766, 2103, 1208, 2058, 2054,
  1145, 1142, 2005, 2002, 1999, 2009, 1488, 1429, 1426,
  2200, 1698, 1659, 1656, 1975, 1053, 1957, 1954, 1001,
  998, 1924, 1921, 1918, 1928,  937,  934,  931, 1879,
  1876, 1873, 1870,  945, 1885, 1882, 1323, 1273, 1270,
  2105, 1202, 1199, 1196, 1211, 2061, 2057, 1576, 1543,
  1540, 1484, 1481, 1478, 1491, 1700
};

const int BitMatrixParser::SYMBOL_TABLE_LENGTH =
    sizeof(BitMatrixParser::SYMBOL_TABLE) / sizeof(int);
}
}
}

// file: zxing/pdf417/decoder/DecodedBitStreamParser.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 * Copyright 2010, 2012 ZXing authors All rights reserved.
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

// #include <stdint.h>
// #include <bigint/BigIntegerUtils.hh>
// #include <zxing/FormatException.h>
// #include <zxing/pdf417/decoder/DecodedBitStreamParser.h>
// #include <zxing/common/DecoderResult.h>

namespace zxing {
namespace pdf417 {
        
const int DecodedBitStreamParser::TEXT_COMPACTION_MODE_LATCH = 900;
const int DecodedBitStreamParser::BYTE_COMPACTION_MODE_LATCH = 901;
const int DecodedBitStreamParser::NUMERIC_COMPACTION_MODE_LATCH = 902;
const int DecodedBitStreamParser::BYTE_COMPACTION_MODE_LATCH_6 = 924;
const int DecodedBitStreamParser::BEGIN_MACRO_PDF417_CONTROL_BLOCK = 928;
const int DecodedBitStreamParser::BEGIN_MACRO_PDF417_OPTIONAL_FIELD = 923;
const int DecodedBitStreamParser::MACRO_PDF417_TERMINATOR = 922;
const int DecodedBitStreamParser::MODE_SHIFT_TO_BYTE_COMPACTION_MODE = 913;
const int DecodedBitStreamParser::MAX_NUMERIC_CODEWORDS = 15;

const int DecodedBitStreamParser::PL = 25;
const int DecodedBitStreamParser::LL = 27;
const int DecodedBitStreamParser::AS = 27;
const int DecodedBitStreamParser::ML = 28;
const int DecodedBitStreamParser::AL = 28;
const int DecodedBitStreamParser::PS = 29;
const int DecodedBitStreamParser::PAL = 29;

const int DecodedBitStreamParser::EXP900_SIZE = 16;

const char DecodedBitStreamParser::PUNCT_CHARS[] = {
  ';', '<', '>', '@', '[', '\\', '}', '_', '`', '~', '!',
  '\r', '\t', ',', ':', '\n', '-', '.', '$', '/', '"', '|', '*',
  '(', ')', '?', '{', '}', '\''};

const char DecodedBitStreamParser::MIXED_CHARS[] = {
  '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '&',
  '\r', '\t', ',', ':', '#', '-', '.', '$', '/', '+', '%', '*',
  '=', '^'};

ArrayRef<BigInteger> DecodedBitStreamParser::initEXP900() {
  ArrayRef<BigInteger> EXP900 (16);
  EXP900[0] = BigInteger(1);
  BigInteger nineHundred (900);
  EXP900[1] = nineHundred;
  for (int i = 2; i < EXP900->size(); i++) {
    EXP900[i] = EXP900[i - 1] * nineHundred;
  }
  return EXP900;
}

ArrayRef<BigInteger> DecodedBitStreamParser::EXP900 = initEXP900();

DecodedBitStreamParser::DecodedBitStreamParser(){}

/**
 * PDF417 main decoder.
 **/
Ref<DecoderResult> DecodedBitStreamParser::decode(ArrayRef<int> codewords)
{
  Ref<String> result (new String(100));
  // Get compaction mode
  int codeIndex = 1;
  int code = codewords[codeIndex++];
  while (codeIndex < codewords[0]) {
    switch (code) {
      case TEXT_COMPACTION_MODE_LATCH:
        codeIndex = textCompaction(codewords, codeIndex, result);
        break;
      case BYTE_COMPACTION_MODE_LATCH:
        codeIndex = byteCompaction(code, codewords, codeIndex, result);
        break;
      case NUMERIC_COMPACTION_MODE_LATCH:
        codeIndex = numericCompaction(codewords, codeIndex, result);
        break;
      case MODE_SHIFT_TO_BYTE_COMPACTION_MODE:
        codeIndex = byteCompaction(code, codewords, codeIndex, result);
        break;
      case BYTE_COMPACTION_MODE_LATCH_6:
        codeIndex = byteCompaction(code, codewords, codeIndex, result);
        break;
      default:
        // Default to text compaction. During testing numerous barcodes
        // appeared to be missing the starting mode. In these cases defaulting
        // to text compaction seems to work.
        codeIndex--;
        codeIndex = textCompaction(codewords, codeIndex, result);
        break;
    }
    if (codeIndex < codewords->size()) {
      code = codewords[codeIndex++];
    } else {
      throw FormatException();
    }
  }
  return Ref<DecoderResult>(new DecoderResult(ArrayRef<char>(), result));
}

/**
 * Text Compaction mode (see 5.4.1.5) permits all printable ASCII characters to be
 * encoded, i.e. values 32 - 126 inclusive in accordance with ISO/IEC 646 (IRV), as
 * well as selected control characters.
 *
 * @param codewords The array of codewords (data + error)
 * @param codeIndex The current index into the codeword array.
 * @param result    The decoded data is appended to the result.
 * @return The next index into the codeword array.
 */
int DecodedBitStreamParser::textCompaction(ArrayRef<int> codewords,
                                           int codeIndex,
                                           Ref<String> result) {
  // 2 character per codeword
  ArrayRef<int> textCompactionData (codewords[0] << 1);
  // Used to hold the byte compaction value if there is a mode shift
  ArrayRef<int> byteCompactionData (codewords[0] << 1);

  int index = 0;
  bool end = false;
  while ((codeIndex < codewords[0]) && !end) {
    int code = codewords[codeIndex++];
    if (code < TEXT_COMPACTION_MODE_LATCH) {
      textCompactionData[index] = code / 30;
      textCompactionData[index + 1] = code % 30;
      index += 2;
    } else {
      switch (code) {
        case TEXT_COMPACTION_MODE_LATCH:
          textCompactionData[index++] = TEXT_COMPACTION_MODE_LATCH;
          break;
        case BYTE_COMPACTION_MODE_LATCH:
          codeIndex--;
          end = true;
          break;
        case NUMERIC_COMPACTION_MODE_LATCH:
          codeIndex--;
          end = true;
          break;
        case MODE_SHIFT_TO_BYTE_COMPACTION_MODE:
          // The Mode Shift codeword 913 shall cause a temporary
          // switch from Text Compaction mode to Byte Compaction mode.
          // This switch shall be in effect for only the next codeword,
          // after which the mode shall revert to the prevailing sub-mode
          // of the Text Compaction mode. Codeword 913 is only available
          // in Text Compaction mode; its use is described in 5.4.2.4.
          textCompactionData[index] = MODE_SHIFT_TO_BYTE_COMPACTION_MODE;
          code = codewords[codeIndex++];
          byteCompactionData[index] = code; //Integer.toHexString(code);
          index++;
          break;
        case BYTE_COMPACTION_MODE_LATCH_6:
          codeIndex--;
          end = true;
          break;
      }
    }
  }
  decodeTextCompaction(textCompactionData, byteCompactionData, index, result);
  return codeIndex;
}

/**
 * The Text Compaction mode includes all the printable ASCII characters
 * (i.e. values from 32 to 126) and three ASCII control characters: HT or tab
 * (ASCII value 9), LF or line feed (ASCII value 10), and CR or carriage
 * return (ASCII value 13). The Text Compaction mode also includes various latch
 * and shift characters which are used exclusively within the mode. The Text
 * Compaction mode encodes up to 2 characters per codeword. The compaction rules
 * for converting data into PDF417 codewords are defined in 5.4.2.2. The sub-mode
 * switches are defined in 5.4.2.3.
 *
 * @param textCompactionData The text compaction data.
 * @param byteCompactionData The byte compaction data if there
 *                           was a mode shift.
 * @param length             The size of the text compaction and byte compaction data.
 * @param result             The decoded data is appended to the result.
 */
void DecodedBitStreamParser::decodeTextCompaction(ArrayRef<int> textCompactionData,
                                                  ArrayRef<int> byteCompactionData,
                                                  int length,
                                                  Ref<String> result)
{
  // Beginning from an initial state of the Alpha sub-mode
  // The default compaction mode for PDF417 in effect at the start of each symbol shall always be Text
  // Compaction mode Alpha sub-mode (uppercase alphabetic). A latch codeword from another mode to the Text
  // Compaction mode shall always switch to the Text Compaction Alpha sub-mode.
  Mode subMode = ALPHA;
  Mode priorToShiftMode = ALPHA;
  int i = 0;
  while (i < length) {
    int subModeCh = textCompactionData[i];
    char ch = 0;
    switch (subMode) {
      case ALPHA:
        // Alpha (uppercase alphabetic)
        if (subModeCh < 26) {
          // Upper case Alpha Character
          ch = (char) ('A' + subModeCh);
        } else {
          if (subModeCh == 26) {
            ch = ' ';
          } else if (subModeCh == LL) {
            subMode = LOWER;
          } else if (subModeCh == ML) {
            subMode = MIXED;
          } else if (subModeCh == PS) {
            // Shift to punctuation
            priorToShiftMode = subMode;
            subMode = PUNCT_SHIFT;
          } else if (subModeCh == MODE_SHIFT_TO_BYTE_COMPACTION_MODE) {
            result->append((char) byteCompactionData[i]);
          } else if (subModeCh == TEXT_COMPACTION_MODE_LATCH) {
            subMode = ALPHA;
          }
        }
        break;

      case LOWER:
        // Lower (lowercase alphabetic)
        if (subModeCh < 26) {
          ch = (char) ('a' + subModeCh);
        } else {
          if (subModeCh == 26) {
            ch = ' ';
          } else if (subModeCh == AS) {
            // Shift to alpha
            priorToShiftMode = subMode;
            subMode = ALPHA_SHIFT;
          } else if (subModeCh == ML) {
            subMode = MIXED;
          } else if (subModeCh == PS) {
            // Shift to punctuation
            priorToShiftMode = subMode;
            subMode = PUNCT_SHIFT;
          } else if (subModeCh == MODE_SHIFT_TO_BYTE_COMPACTION_MODE) {
            result->append((char) byteCompactionData[i]);
          } else if (subModeCh == TEXT_COMPACTION_MODE_LATCH) {
            subMode = ALPHA;
          }
        }
        break;

      case MIXED:
        // Mixed (numeric and some punctuation)
        if (subModeCh < PL) {
          ch = MIXED_CHARS[subModeCh];
        } else {
          if (subModeCh == PL) {
            subMode = PUNCT;
          } else if (subModeCh == 26) {
            ch = ' ';
          } else if (subModeCh == LL) {
            subMode = LOWER;
          } else if (subModeCh == AL) {
            subMode = ALPHA;
          } else if (subModeCh == PS) {
            // Shift to punctuation
            priorToShiftMode = subMode;
            subMode = PUNCT_SHIFT;
          } else if (subModeCh == MODE_SHIFT_TO_BYTE_COMPACTION_MODE) {
            result->append((char) byteCompactionData[i]);
          } else if (subModeCh == TEXT_COMPACTION_MODE_LATCH) {
            subMode = ALPHA;
          }
        }
        break;

      case PUNCT:
        // Punctuation
        if (subModeCh < PAL) {
          ch = PUNCT_CHARS[subModeCh];
        } else {
          if (subModeCh == PAL) {
            subMode = ALPHA;
          } else if (subModeCh == MODE_SHIFT_TO_BYTE_COMPACTION_MODE) {
            result->append((char) byteCompactionData[i]);
          } else if (subModeCh == TEXT_COMPACTION_MODE_LATCH) {
            subMode = ALPHA;
          }
        }
        break;

      case ALPHA_SHIFT:
        // Restore sub-mode
        subMode = priorToShiftMode;
        if (subModeCh < 26) {
          ch = (char) ('A' + subModeCh);
        } else {
          if (subModeCh == 26) {
            ch = ' ';
          } else {
            if (subModeCh == 26) {
              ch = ' ';
            } else if (subModeCh == TEXT_COMPACTION_MODE_LATCH) {
              subMode = ALPHA;
            }
          }
        }
        break;

      case PUNCT_SHIFT:
        // Restore sub-mode
        subMode = priorToShiftMode;
        if (subModeCh < PAL) {
          ch = PUNCT_CHARS[subModeCh];
        } else {
          if (subModeCh == PAL) {
            subMode = ALPHA;
            // 2012-11-27 added from recent java code:
          } else if (subModeCh == MODE_SHIFT_TO_BYTE_COMPACTION_MODE) {
            // PS before Shift-to-Byte is used as a padding character,
            // see 5.4.2.4 of the specification
            result->append((char) byteCompactionData[i]);
          } else if (subModeCh == TEXT_COMPACTION_MODE_LATCH) {
            subMode = ALPHA;
          }
        }
        break;
    }
    if (ch != 0) {
      // Append decoded character to result
      result->append(ch);
    }
    i++;
  }
}

/**
 * Byte Compaction mode (see 5.4.3) permits all 256 possible 8-bit byte values to be encoded.
 * This includes all ASCII characters value 0 to 127 inclusive and provides for international
 * character set support.
 *
 * @param mode      The byte compaction mode i.e. 901 or 924
 * @param codewords The array of codewords (data + error)
 * @param codeIndex The current index into the codeword array.
 * @param result    The decoded data is appended to the result.
 * @return The next index into the codeword array.
 */
int DecodedBitStreamParser::byteCompaction(int mode,
                                           ArrayRef<int> codewords,
                                           int codeIndex, Ref<String> result) {
  if (mode == BYTE_COMPACTION_MODE_LATCH) {
    // Total number of Byte Compaction characters to be encoded
    // is not a multiple of 6
    int count = 0;
    int64_t value = 0;
    ArrayRef<char> decodedData = new Array<char>(6);
    ArrayRef<int> byteCompactedCodewords = new Array<int>(6);
    bool end = false;
    int nextCode = codewords[codeIndex++];
    while ((codeIndex < codewords[0]) && !end) {
      byteCompactedCodewords[count++] = nextCode;
      // Base 900
      value = 900 * value + nextCode;
      nextCode = codewords[codeIndex++];
      // perhaps it should be ok to check only nextCode >= TEXT_COMPACTION_MODE_LATCH
      if (nextCode == TEXT_COMPACTION_MODE_LATCH ||
          nextCode == BYTE_COMPACTION_MODE_LATCH ||
          nextCode == NUMERIC_COMPACTION_MODE_LATCH ||
          nextCode == BYTE_COMPACTION_MODE_LATCH_6 ||
          nextCode == BEGIN_MACRO_PDF417_CONTROL_BLOCK ||
          nextCode == BEGIN_MACRO_PDF417_OPTIONAL_FIELD ||
          nextCode == MACRO_PDF417_TERMINATOR)
      {
        end = true;
      }
      else
      {
        if ((count%5 == 0) && (count > 0))
        {
          // Decode every 5 codewords
          // Convert to Base 256
          for (int j = 0; j < 6; ++j)
          {
            decodedData[5 - j] = (char) (value%256);
            value >>= 8;
          }
          result->append(string(&(decodedData->values()[0]), decodedData->values().size()));
          count = 0;
        }
      }
    }

    // if the end of all codewords is reached the last codeword needs to be added
    if (codeIndex == codewords[0] && nextCode < TEXT_COMPACTION_MODE_LATCH)
      byteCompactedCodewords[count++] = nextCode;

    // If Byte Compaction mode is invoked with codeword 901,
    // the last group of codewords is interpreted directly
    // as one byte per codeword, without compaction.
    for (int i = 0; i < count; i++)
    {
      result->append((char)byteCompactedCodewords[i]);
    }

  } else if (mode == BYTE_COMPACTION_MODE_LATCH_6) {
    // Total number of Byte Compaction characters to be encoded
    // is an integer multiple of 6
    int count = 0;
    int64_t value = 0;
    bool end = false;
    while (codeIndex < codewords[0] && !end) {
      int code = codewords[codeIndex++];
      if (code < TEXT_COMPACTION_MODE_LATCH) {
        count++;
        // Base 900
        value = 900 * value + code;
      } else {
        if (code == TEXT_COMPACTION_MODE_LATCH ||
            code == BYTE_COMPACTION_MODE_LATCH ||
            code == NUMERIC_COMPACTION_MODE_LATCH ||
            code == BYTE_COMPACTION_MODE_LATCH_6 ||
            code == BEGIN_MACRO_PDF417_CONTROL_BLOCK ||
            code == BEGIN_MACRO_PDF417_OPTIONAL_FIELD ||
            code == MACRO_PDF417_TERMINATOR) {
          codeIndex--;
          end = true;
        }
      }
      if ((count % 5 == 0) && (count > 0)) {
        // Decode every 5 codewords
        // Convert to Base 256
        ArrayRef<char> decodedData = new Array<char>(6);
        for (int j = 0; j < 6; ++j) {
          decodedData[5 - j] = (char) (value & 0xFF);
          value >>= 8;
        }
        result->append(string(&decodedData[0],6));
        // 2012-11-27 hfn after recent java code/fix by srowen
        count = 0;
      }
    }
  }
  return codeIndex;
}

/**
 * Numeric Compaction mode (see 5.4.4) permits efficient encoding of numeric data strings.
 *
 * @param codewords The array of codewords (data + error)
 * @param codeIndex The current index into the codeword array.
 * @param result    The decoded data is appended to the result.
 * @return The next index into the codeword array.
 */
int DecodedBitStreamParser::numericCompaction(ArrayRef<int> codewords,
                                              int codeIndex,
                                              Ref<String> result) {
  int count = 0;
  bool end = false;

  ArrayRef<int> numericCodewords = new Array<int>(MAX_NUMERIC_CODEWORDS);

  while (codeIndex < codewords[0] && !end) {
    int code = codewords[codeIndex++];
    if (codeIndex == codewords[0]) {
      end = true;
    }
    if (code < TEXT_COMPACTION_MODE_LATCH) {
      numericCodewords[count] = code;
      count++;
    } else {
      if (code == TEXT_COMPACTION_MODE_LATCH ||
          code == BYTE_COMPACTION_MODE_LATCH ||
          code == BYTE_COMPACTION_MODE_LATCH_6 ||
          code == BEGIN_MACRO_PDF417_CONTROL_BLOCK ||
          code == BEGIN_MACRO_PDF417_OPTIONAL_FIELD ||
          code == MACRO_PDF417_TERMINATOR) {
        codeIndex--;
        end = true;
      }
    }
    if (count % MAX_NUMERIC_CODEWORDS == 0 ||
        code == NUMERIC_COMPACTION_MODE_LATCH ||
        end) {
      // Re-invoking Numeric Compaction mode (by using codeword 902
      // while in Numeric Compaction mode) serves  to terminate the
      // current Numeric Compaction mode grouping as described in 5.4.4.2,
      // and then to start a new one grouping.
      Ref<String> s = decodeBase900toBase10(numericCodewords, count);
      result->append(s->getText());
      count = 0;
    }
  }
  return codeIndex;
}

/**
 * Convert a list of Numeric Compacted codewords from Base 900 to Base 10.
 *
 * @param codewords The array of codewords
 * @param count     The number of codewords
 * @return The decoded string representing the Numeric data.
 */
/*
  EXAMPLE
  Encode the fifteen digit numeric string 000213298174000
  Prefix the numeric string with a 1 and set the initial value of
  t = 1 000 213 298 174 000
  Calculate codeword 0
  d0 = 1 000 213 298 174 000 mod 900 = 200

  t = 1 000 213 298 174 000 div 900 = 1 111 348 109 082
  Calculate codeword 1
  d1 = 1 111 348 109 082 mod 900 = 282

  t = 1 111 348 109 082 div 900 = 1 234 831 232
  Calculate codeword 2
  d2 = 1 234 831 232 mod 900 = 632

  t = 1 234 831 232 div 900 = 1 372 034
  Calculate codeword 3
  d3 = 1 372 034 mod 900 = 434

  t = 1 372 034 div 900 = 1 524
  Calculate codeword 4
  d4 = 1 524 mod 900 = 624

  t = 1 524 div 900 = 1
  Calculate codeword 5
  d5 = 1 mod 900 = 1
  t = 1 div 900 = 0
  Codeword sequence is: 1, 624, 434, 632, 282, 200

  Decode the above codewords involves
  1 x 900 power of 5 + 624 x 900 power of 4 + 434 x 900 power of 3 +
  632 x 900 power of 2 + 282 x 900 power of 1 + 200 x 900 power of 0 = 1000213298174000

  Remove leading 1 =>  Result is 000213298174000
*/
Ref<String> DecodedBitStreamParser::decodeBase900toBase10(ArrayRef<int> codewords, int count)
{
  BigInteger result = BigInteger(0);
  for (int i = 0; i < count; i++) {
    result = result + (EXP900[count - i - 1] * BigInteger(codewords[i]));
  }
  string resultString = bigIntegerToString(result);
  if (resultString[0] != '1') {
    throw FormatException("DecodedBitStreamParser::decodeBase900toBase10: String does not begin with 1");
  }
  string resultString2;
  resultString2.assign(resultString.begin()+1,resultString.end());
  Ref<String> res (new String(resultString2));
  return res;
}
}
}

// file: zxing/pdf417/decoder/Decoder.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 * Copyright 2010, 2012 ZXing authors All rights reserved.
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
 * 2012-06-27 hfn: PDF417 Reed-Solomon error correction, using following Java
 * source code:
 * http://code.google.com/p/zxing/issues/attachmentText?id=817&aid=8170033000&name=pdf417-java-reed-solomon-error-correction-2.patch&token=0819f5d7446ae2814fd91385eeec6a11
 */

// #include <zxing/pdf417/PDF417Reader.h>
// #include <zxing/pdf417/decoder/Decoder.h>
// #include <zxing/pdf417/decoder/BitMatrixParser.h>
// #include <zxing/pdf417/decoder/DecodedBitStreamParser.h>
// #include <zxing/ReaderException.h>
// #include <zxing/common/reedsolomon/ReedSolomonException.h>

namespace zxing {
namespace pdf417 {
namespace decoder {
            
const int Decoder::MAX_ERRORS = 3;
const int Decoder::MAX_EC_CODEWORDS = 512;

Ref<DecoderResult> Decoder::decode(Ref<BitMatrix> bits, DecodeHints const& hints) {
  (void)hints;
  // Construct a parser to read the data codewords and error-correction level
  BitMatrixParser parser(bits);
  ArrayRef<int> codewords(parser.readCodewords());
  if (codewords->size() == 0) {
    throw FormatException("PDF:Decoder:decode: cannot read codewords");
  }

  int ecLevel = parser.getECLevel();
  int numECCodewords = 1 << (ecLevel + 1);
  ArrayRef<int> erasures = parser.getErasures();

  correctErrors(codewords, erasures, numECCodewords);
  verifyCodewordCount(codewords, numECCodewords);

  // Decode the codewords
  return DecodedBitStreamParser::decode(codewords);
}

/**
 * Verify that all is OK with the codeword array.
 *
 * @param codewords
 * @return an index to the first data codeword.
 * @throws FormatException
 */
void Decoder::verifyCodewordCount(ArrayRef<int> codewords, int numECCodewords) {
  int cwsize = (int)codewords->size();
  if (cwsize < 4) {
    // Codeword array size should be at least 4 allowing for
    // Count CW, At least one Data CW, Error Correction CW, Error Correction CW
    throw FormatException("PDF:Decoder:verifyCodewordCount: codeword array too small!");
  }
  // The first codeword, the Symbol Length Descriptor, shall always encode the total number of data
  // codewords in the symbol, including the Symbol Length Descriptor itself, data codewords and pad
  // codewords, but excluding the number of error correction codewords.
  int numberOfCodewords = codewords[0];
  if (numberOfCodewords > cwsize) {
    throw FormatException("PDF:Decoder:verifyCodewordCount: bad codeword number descriptor!");
  }
  if (numberOfCodewords == 0) {
    // Reset to the length of the array - 8 (Allow for at least level 3 Error Correction (8 Error Codewords)
    if (numECCodewords < cwsize) {
      codewords[0] = cwsize - numECCodewords;
    } else {
      throw FormatException("PDF:Decoder:verifyCodewordCount: bad error correction cw number!");
    }
  }
}

/**
 * Correct errors whenever it is possible using Reed-Solomom algorithm
 *
 * @param codewords, erasures, numECCodewords
 * @return 0.
 * @throws FormatException
 */
void Decoder::correctErrors(ArrayRef<int> codewords,
                            ArrayRef<int> erasures, int numECCodewords) {
  if (erasures->size() > numECCodewords / 2 + MAX_ERRORS ||
      numECCodewords < 0 || numECCodewords > MAX_EC_CODEWORDS) {
    throw FormatException("PDF:Decoder:correctErrors: Too many errors or EC Codewords corrupted");
  }

  Ref<ec::ErrorCorrection> errorCorrection(new ec::ErrorCorrection);
  errorCorrection->decode(codewords, numECCodewords, erasures);

  // 2012-06-27 HFN if, despite of error correction, there are still codewords with invalid
  // value, throw an exception here:
  for (int i = 0; i < codewords->size(); i++) {
    if (codewords[i]<0) {
      throw FormatException("PDF:Decoder:correctErrors: Error correction did not succeed!");
    }
  }
}
}
}
}

// file: zxing/pdf417/decoder/ec/ErrorCorrection.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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
 * 2012-09-19 HFN translation from Java into C++
 */

// #include <zxing/pdf417/decoder/ec/ErrorCorrection.h>
// #include <zxing/pdf417/decoder/ec/ModulusPoly.h>
// #include <zxing/pdf417/decoder/ec/ModulusGF.h>

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


ErrorCorrection::ErrorCorrection()
    : field_(ModulusGF::PDF417_GF)
{
}

void ErrorCorrection::decode(ArrayRef<int> received,
                             int numECCodewords,
                             ArrayRef<int> erasures)
{
  Ref<ModulusPoly> poly (new ModulusPoly(field_, received));
  ArrayRef<int> S( new Array<int>(numECCodewords));
  bool error = false;
  for (int i = numECCodewords; i > 0; i--) {
    int eval = poly->evaluateAt(field_.exp(i));
    S[numECCodewords - i] = eval;
    if (eval != 0) {
      error = true;
    }
  }

  if (error) {

    Ref<ModulusPoly> knownErrors = field_.getOne();
    for (int i=0;i<erasures->size();i++) {
      int b = field_.exp((int)received->size() - 1 - erasures[i]);
      // Add (1 - bx) term:
      ArrayRef<int> one_minus_b_x(new Array<int>(2));
      one_minus_b_x[1]=field_.subtract(0,b);
      one_minus_b_x[0]=1;
      Ref<ModulusPoly> term (new ModulusPoly(field_,one_minus_b_x));
      knownErrors = knownErrors->multiply(term);
    }

    Ref<ModulusPoly> syndrome (new ModulusPoly(field_, S));
    //syndrome = syndrome.multiply(knownErrors);

    vector<Ref<ModulusPoly> > sigmaOmega (
        runEuclideanAlgorithm(field_.buildMonomial(numECCodewords, 1), syndrome, numECCodewords));
    Ref<ModulusPoly> sigma = sigmaOmega[0];
    Ref<ModulusPoly> omega = sigmaOmega[1];

    //sigma = sigma.multiply(knownErrors);

    ArrayRef<int> errorLocations = findErrorLocations(sigma);
    ArrayRef<int> errorMagnitudes = findErrorMagnitudes(omega, sigma, errorLocations);

    for (int i = 0; i < errorLocations->size(); i++) {
      int position = (int)received->size() - 1 - field_.log(errorLocations[i]);
      if (position < 0) {
        throw ReedSolomonException("Bad error location!");
      }
      received[position] = field_.subtract(received[position], errorMagnitudes[i]);
#if (defined (DEBUG)  && defined _WIN32)
      {
        WCHAR szmsg[256];
        swprintf(szmsg,L"ErrorCorrection::decode: fix @ %d, new value = %d\n",
                 position, received[position]);
        OutputDebugString(szmsg);
      }
#endif
    }
  }
}

vector<Ref<ModulusPoly> >  ErrorCorrection::runEuclideanAlgorithm(Ref<ModulusPoly> a, Ref<ModulusPoly> b, int R)
{
  // Assume a's degree is >= b's
  if (a->getDegree() < b->getDegree()) {
    Ref<ModulusPoly> temp = a;
    a = b;
    b = temp;
  }

  Ref<ModulusPoly> rLast ( a);
  Ref<ModulusPoly> r ( b);
  Ref<ModulusPoly> tLast ( field_.getZero());
  Ref<ModulusPoly> t ( field_.getOne());

  // Run Euclidean algorithm until r's degree is less than R/2
  while (r->getDegree() >= R / 2) {
    Ref<ModulusPoly> rLastLast (rLast);
    Ref<ModulusPoly> tLastLast (tLast);
    rLast = r;
    tLast = t;

    // Divide rLastLast by rLast, with quotient in q and remainder in r
    if (rLast->isZero()) {
      // Oops, Euclidean algorithm already terminated?
      throw ReedSolomonException("Euclidean algorithm already terminated?");
    }
    r = rLastLast;
    Ref<ModulusPoly> q (field_.getZero());
    int denominatorLeadingTerm = rLast->getCoefficient(rLast->getDegree());
    int dltInverse = field_.inverse(denominatorLeadingTerm);
    while (r->getDegree() >= rLast->getDegree() && !r->isZero()) {
      int degreeDiff = r->getDegree() - rLast->getDegree();
      int scale = field_.multiply(r->getCoefficient(r->getDegree()), dltInverse);
      q = q->add(field_.buildMonomial(degreeDiff, scale));
      r = r->subtract(rLast->multiplyByMonomial(degreeDiff, scale));
    }

	  t = q->multiply(tLast)->subtract(tLastLast)->negative();
  }

  int sigmaTildeAtZero = t->getCoefficient(0);
  if (sigmaTildeAtZero == 0) {
    throw ReedSolomonException("sigmaTilde = 0!");
  }

  int inverse = field_.inverse(sigmaTildeAtZero);
  Ref<ModulusPoly> sigma (t->multiply(inverse));
  Ref<ModulusPoly> omega (r->multiply(inverse));
	vector<Ref<ModulusPoly> > v(2);
	v[0] = sigma;
	v[1] = omega;
  return v;
}

ArrayRef<int> ErrorCorrection::findErrorLocations(Ref<ModulusPoly> errorLocator)  {
  // This is a direct application of Chien's search
  int numErrors = errorLocator->getDegree();
  ArrayRef<int> result( new Array<int>(numErrors));
  int e = 0;
  for (int i = 1; i < field_.getSize() && e < numErrors; i++) {
    if (errorLocator->evaluateAt(i) == 0) {
      result[e] = field_.inverse(i);
      e++;
    }
  }
  if (e != numErrors) {
#if (defined (DEBUG) && defined _WIN32)
	  char sz[128];
	  sprintf(sz,"Error number inconsistency, %d/%d!",e,numErrors);
    throw ReedSolomonException(sz);
#else
	  throw ReedSolomonException("Error number inconsistency!");
#endif
  }
#if (defined (DEBUG) && defined _WIN32)
  {
    WCHAR szmsg[256];
    swprintf(szmsg,L"ErrorCorrection::findErrorLocations: found %d errors.\n",
             e);
    OutputDebugString(szmsg);
  }
#endif
  return result;
}

ArrayRef<int> ErrorCorrection::findErrorMagnitudes(Ref<ModulusPoly> errorEvaluator,
                                                   Ref<ModulusPoly> errorLocator,
                                                   ArrayRef<int> errorLocations) {
	int i;
  int errorLocatorDegree = errorLocator->getDegree();
  ArrayRef<int> formalDerivativeCoefficients (new Array<int>(errorLocatorDegree));
  for (i = 1; i <= errorLocatorDegree; i++) {
    formalDerivativeCoefficients[errorLocatorDegree - i] =
        field_.multiply(i, errorLocator->getCoefficient(i));
  }
  Ref<ModulusPoly> formalDerivative (new ModulusPoly(field_, formalDerivativeCoefficients));

  // This is directly applying Forney's Formula
  int s = (int)errorLocations->size();
  ArrayRef<int> result ( new Array<int>(s));
  for (i = 0; i < s; i++) {
    int xiInverse = field_.inverse(errorLocations[i]);
    int numerator = field_.subtract(0, errorEvaluator->evaluateAt(xiInverse));
    int denominator = field_.inverse(formalDerivative->evaluateAt(xiInverse));
    result[i] = field_.multiply(numerator, denominator);
  }
  return result;
}
}
}
}
}

// file: zxing/pdf417/decoder/ec/ModulusGF.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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
 * 2012-09-19 HFN translation from Java into C++
 */

// #include <zxing/pdf417/decoder/ec/ModulusGF.h>
// #include <zxing/pdf417/decoder/ec/ModulusPoly.h>

namespace zxing {
namespace pdf417 {
namespace decoder {
namespace ec {
                
                
 /**
 * The central Modulus Galois Field for PDF417 with prime number 929
 * and generator 3.
 */
ModulusGF ModulusGF::PDF417_GF(929,3);


/**
 * <p>A field based on powers of a generator integer, modulo some modulus.</p>
 *
 * @author Sean Owen
 * @see com.google.zxing.common.reedsolomon.GenericGF
 */

ModulusGF::ModulusGF(int modulus, int generator)
    : modulus_(modulus) {
	expTable_ = new Array<int>(modulus_);
	logTable_ = new Array<int>(modulus_);
  int x = 1,i;
  for (i = 0; i < modulus_; i++) {
    expTable_[i] = x;
    x = (x * generator) % modulus_;
  }
  for (i = 0; i < modulus_-1; i++) {
    logTable_[expTable_[i]] = i;
  }
  // logTable[0] == 0 but this should never be used
	ArrayRef<int>aZero(new Array<int>(1)),aOne(new Array<int>(1));
	aZero[0]=0;aOne[0]=1;
  zero_ = new ModulusPoly(*this, aZero);
  one_ = new ModulusPoly(*this, aOne);
}

Ref<ModulusPoly> ModulusGF::getZero() {
  return zero_;
}

Ref<ModulusPoly> ModulusGF::getOne() {
  return one_;
}

Ref<ModulusPoly> ModulusGF::buildMonomial(int degree, int coefficient)
{
  if (degree < 0) {
    throw IllegalArgumentException("monomial: degree < 0!");
  }
  if (coefficient == 0) {
    return zero_;
  }
	int nCoefficients = degree + 1;
  ArrayRef<int> coefficients (new Array<int>(nCoefficients));
  coefficients[0] = coefficient;
	Ref<ModulusPoly> result(new ModulusPoly(*this,coefficients));
  return result;
}



int ModulusGF::add(int a, int b) {
  return (a + b) % modulus_;
}

int ModulusGF::subtract(int a, int b) {
  return (modulus_ + a - b) % modulus_;
}

int ModulusGF::exp(int a) {
  return expTable_[a];
}

int ModulusGF::log(int a) {
  if (a == 0) {
    throw IllegalArgumentException("log of zero!");
  }
  return logTable_[a];
}

int ModulusGF::inverse(int a) {
  if (a == 0) {
    throw IllegalArgumentException("inverse of zero!");;
  }
  return expTable_[modulus_ - logTable_[a] - 1];
}

int ModulusGF::multiply(int a, int b) {
  if (a == 0 || b == 0) {
    return 0;
  }
  return expTable_[(logTable_[a] + logTable_[b]) % (modulus_ - 1)];
}

int ModulusGF::getSize() {
  return modulus_;
}
}
}
}
}

// file: zxing/pdf417/decoder/ec/ModulusPoly.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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
 * 2012-09-19 HFN translation from Java into C++
 */

// #include <zxing/pdf417/decoder/ec/ModulusPoly.h>
// #include <zxing/pdf417/decoder/ec/ModulusGF.h>

namespace zxing {
namespace pdf417 {
namespace decoder {
namespace ec {

 /**
 * @author Sean Owen
 * @see com.google.zxing.common.reedsolomon.GenericGFPoly
 */

ModulusPoly::ModulusPoly(ModulusGF& field, ArrayRef<int> coefficients)
    : field_(field)
{
  if (coefficients->size() == 0) {
    throw IllegalArgumentException("no coefficients!");
  }
  size_t coefficientsLength = coefficients->size();
  if (coefficientsLength > 1 && coefficients[0] == 0) {
    // Leading term must be non-zero for anything except the constant polynomial "0"
    int firstNonZero = 1;
    while (firstNonZero < coefficientsLength && coefficients[firstNonZero] == 0) {
      firstNonZero++;
    }
    if (firstNonZero == coefficientsLength) {
	    coefficientsLength = field_.getZero()->getCoefficients()->size();
      coefficients_.reset(new Array<int> ((int)coefficientsLength));
      *coefficients_ = *(field_.getZero()->getCoefficients());
    } else {
      ArrayRef<int> c(coefficients);
      coefficientsLength -= firstNonZero;
      coefficients_.reset(new Array<int> ((int)coefficientsLength));
      for (int i = 0; i < coefficientsLength; i++) {
        coefficients_[i] = c[i + firstNonZero];
      }
      /*
        coefficientsLength -= firstNonZero;
        coefficients_.reset(new Array<int>(coefficientsLength - firstNonZero));
        for (int i = 0; i < coefficientsLength; i++) {
        coefficients_[i] = coefficients[i + firstNonZero];
        }
      */
    }
  } else {
    coefficients_ = coefficients;
  }
}

ArrayRef<int> ModulusPoly::getCoefficients() {
  return coefficients_;
}

/**
 * @return degree of this polynomial
 */
int ModulusPoly::getDegree() {
  return (int)coefficients_->size() - 1;
}

/**
 * @return true iff this polynomial is the monomial "0"
 */
bool ModulusPoly::isZero() {
  return coefficients_[0] == 0;
}

/**
 * @return coefficient of x^degree term in this polynomial
 */
int ModulusPoly::getCoefficient(int degree) {
  return coefficients_[(int)coefficients_->size() - 1 - degree];
}

/**
 * @return evaluation of this polynomial at a given point
 */
int ModulusPoly::evaluateAt(int a) {
	int i;
  if (a == 0) {
    // Just return the x^0 coefficient
    return getCoefficient(0);
  }
  size_t size = coefficients_->size();
  if (a == 1) {
    // Just the sum of the coefficients
    int result = 0;
	  for (i = 0; i < size; i++) {
      result = field_.add(result, coefficients_[i]);
	  }
    return result;
  }
  int result = coefficients_[0];
  for (i = 1; i < size; i++) {
    result = field_.add(field_.multiply(a, result), coefficients_[i]);
  }
  return result;
}

Ref<ModulusPoly> ModulusPoly::add(Ref<ModulusPoly> other) {
  if (&field_ != &other->field_) {
    throw IllegalArgumentException("ModulusPolys do not have same ModulusGF field");
  }
  if (isZero()) {
    return other;
  }
  if (other->isZero()) {
    return Ref<ModulusPoly>(this);
  }

  ArrayRef<int> smallerCoefficients = coefficients_;
  ArrayRef<int> largerCoefficients = other->coefficients_;
  if (smallerCoefficients->size() > largerCoefficients->size()) {
    ArrayRef<int> temp(smallerCoefficients);
    smallerCoefficients = largerCoefficients;
    largerCoefficients = temp;
  }
  ArrayRef<int>  sumDiff (new Array<int>((int)largerCoefficients->size()));
  int lengthDiff = (int)(largerCoefficients->size() - smallerCoefficients->size());
  // Copy high-order terms only found in higher-degree polynomial's coefficients
	for (int i = 0; i < lengthDiff; i++) {
		sumDiff[i] = largerCoefficients[i];
	}

  for (int i = lengthDiff; i < largerCoefficients->size(); i++) {
    sumDiff[i] = field_.add(smallerCoefficients[i - lengthDiff], largerCoefficients[i]);
  }

  return Ref<ModulusPoly>(new ModulusPoly(field_, sumDiff));
}

Ref<ModulusPoly> ModulusPoly::subtract(Ref<ModulusPoly> other) {
  if (&field_ != &other->field_) {
    throw new IllegalArgumentException("ModulusPolys do not have same ModulusGF field");
  }
  if (other->isZero()) {
    return Ref<ModulusPoly>(this);
  }
  return add(other->negative());
}

Ref<ModulusPoly> ModulusPoly::multiply(Ref<ModulusPoly> other) {
  if (&field_ != &other->field_) {
    throw new IllegalArgumentException("ModulusPolys do not have same ModulusGF field");
  }
  if (isZero() || other->isZero()) {
    return field_.getZero();
  }
	int i,j;
  ArrayRef<int> aCoefficients = coefficients_;
  size_t aLength = aCoefficients->size();
  ArrayRef<int> bCoefficients = other->coefficients_;
  size_t bLength = bCoefficients->size();
  ArrayRef<int> product (new Array<int>((int)(aLength + bLength - 1)));
  for (i = 0; i < aLength; i++) {
    int aCoeff = aCoefficients[i];
    for (j = 0; j < bLength; j++) {
      product[i + j] = field_.add(product[i + j], field_.multiply(aCoeff, bCoefficients[j]));
    }
  }
  return Ref<ModulusPoly>(new ModulusPoly(field_, product));
}

Ref<ModulusPoly> ModulusPoly::negative() {
  int size = (int)coefficients_->size();
  ArrayRef<int> negativeCoefficients (new Array<int>(size));
  for (int i = 0; i < size; i++) {
    negativeCoefficients[i] = field_.subtract(0, coefficients_[i]);
  }
  return Ref<ModulusPoly>(new ModulusPoly(field_, negativeCoefficients));
}

Ref<ModulusPoly> ModulusPoly::multiply(int scalar) {
  if (scalar == 0) {
    return field_.getZero();
  }
  if (scalar == 1) {
    return Ref<ModulusPoly>(this);
  }
  int size = (int)coefficients_->size();
  ArrayRef<int> product( new Array<int>(size));
  for (int i = 0; i < size; i++) {
    product[i] = field_.multiply(coefficients_[i], scalar);
  }
  return Ref<ModulusPoly>(new ModulusPoly(field_, product));
}

Ref<ModulusPoly> ModulusPoly::multiplyByMonomial(int degree, int coefficient) {
  if (degree < 0) {
    throw new IllegalArgumentException("negative degree!");
  }
  if (coefficient == 0) {
    return field_.getZero();
  }
  int size = (int)coefficients_->size();
  ArrayRef<int> product (new Array<int>(size + degree));
  for (int i = 0; i < size; i++) {
    product[i] = field_.multiply(coefficients_[i], coefficient);
  }
  return Ref<ModulusPoly>(new ModulusPoly(field_, product));
}

std::vector<Ref<ModulusPoly> > ModulusPoly::divide(Ref<ModulusPoly> other) {
  if (&field_ != &other->field_) {
    throw new IllegalArgumentException("ModulusPolys do not have same ModulusGF field");
  }
  if (other->isZero()) {
    throw new IllegalArgumentException("Divide by 0");
  }

  Ref<ModulusPoly> quotient (field_.getZero());
  Ref<ModulusPoly> remainder (this);

  int denominatorLeadingTerm = other->getCoefficient(other->getDegree());
  int inverseDenominatorLeadingTerm = field_.inverse(denominatorLeadingTerm);

  while (remainder->getDegree() >= other->getDegree() && !remainder->isZero()) {
    int degreeDifference = remainder->getDegree() - other->getDegree();
    int scale = field_.multiply(remainder->getCoefficient(remainder->getDegree()), inverseDenominatorLeadingTerm);
    Ref<ModulusPoly> term (other->multiplyByMonomial(degreeDifference, scale));
    Ref<ModulusPoly> iterationQuotient (field_.buildMonomial(degreeDifference, scale));
    quotient = quotient->add(iterationQuotient);
    remainder = remainder->subtract(term);
  }

	std::vector<Ref<ModulusPoly> > result(2);
	result[0] = quotient;
	result[1] = remainder;
  return result;
}

#if 0
@Override
public String toString() {
  StringBuilder result = new StringBuilder(8 * getDegree());
  for (int degree = getDegree(); degree >= 0; degree--) {
    int coefficient = getCoefficient(degree);
    if (coefficient != 0) {
      if (coefficient < 0) {
        result.append(" - ");
        coefficient = -coefficient;
      } else {
        if (result.length() > 0) {
          result.append(" + ");
        }
      }
      if (degree == 0 || coefficient != 1) {
        result.append(coefficient);
      }
      if (degree != 0) {
        if (degree == 1) {
          result.append('x');
        } else {
          result.append("x^");
          result.append(degree);
        }
      }
    }
  }
  return result.toString();
}
#endif

ModulusPoly::~ModulusPoly() {}
}
}
}
}

// file: zxing/pdf417/detector/Detector.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
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

// #include <limits>
// #include <zxing/pdf417/detector/Detector.h>
// #include <zxing/pdf417/detector/LinesSampler.h>
// #include <zxing/common/GridSampler.h>
// #include <zxing/common/detector/JavaMath.h>
// #include <zxing/common/detector/MathUtils.h>
// #include <algorithm>  // vs12, std::min und std:max

namespace zxing {
namespace pdf417 {
namespace detector {
            
 /**
 * <p>Encapsulates logic that can detect a PDF417 Code in an image, even if the
 * PDF417 Code is rotated or skewed, or partially obscured.</p>
 *
 * @author SITA Lab (kevin.osullivan@sita.aero)
 * @author Daniel Switkin (dswitkin@google.com)
 * @author Schweers Informationstechnologie GmbH (hartmut.neubauer@schweers.de)
 * @author creatale GmbH (christoph.schulz@creatale.de)
 */

const int Detector::MAX_AVG_VARIANCE= (int) (PATTERN_MATCH_RESULT_SCALE_FACTOR * 0.42f);
const int Detector::MAX_INDIVIDUAL_VARIANCE = (int) (PATTERN_MATCH_RESULT_SCALE_FACTOR * 0.8f);

// B S B S B S B S Bar/Space pattern
// 11111111 0 1 0 1 0 1 000
const int Detector::START_PATTERN[] = {8, 1, 1, 1, 1, 1, 1, 3};
const int Detector::START_PATTERN_LENGTH = sizeof(START_PATTERN) / sizeof(int);

// 11111111 0 1 0 1 0 1 000
const int Detector::START_PATTERN_REVERSE[] = {3, 1, 1, 1, 1, 1, 1, 8};
const int Detector::START_PATTERN_REVERSE_LENGTH = sizeof(START_PATTERN_REVERSE) / sizeof(int);

// 1111111 0 1 000 1 0 1 00 1
const int Detector::STOP_PATTERN[] = {7, 1, 1, 3, 1, 1, 1, 2, 1};
const int Detector::STOP_PATTERN_LENGTH = sizeof(STOP_PATTERN) / sizeof(int);

// B S B S B S B S B Bar/Space pattern
// 1111111 0 1 000 1 0 1 00 1
const int Detector::STOP_PATTERN_REVERSE[] = {1, 2, 1, 1, 1, 3, 1, 1, 7};
const int Detector::STOP_PATTERN_REVERSE_LENGTH = sizeof(STOP_PATTERN_REVERSE) / sizeof(int);

Detector::Detector(Ref<BinaryBitmap> image) : image_(image) {}

Ref<DetectorResult> Detector::detect() {
  return detect(DecodeHints());
}

Ref<DetectorResult> Detector::detect(DecodeHints const& hints) {
  (void)hints;
  // Fetch the 1 bit matrix once up front.
  Ref<BitMatrix> matrix = image_->getBlackMatrix();

  // Try to find the vertices assuming the image is upright.
  const int rowStep = 8;
  ArrayRef< Ref<ResultPoint> > vertices (findVertices(matrix, rowStep));
  if (!vertices) {
    // Maybe the image is rotated 180 degrees?
    vertices = findVertices180(matrix, rowStep);
    if (vertices) {
      correctVertices(matrix, vertices, true);
    }
  } else {
    correctVertices(matrix, vertices, false);
  }

  if (!vertices) {
    throw NotFoundException("No vertices found.");
  }

  float moduleWidth = computeModuleWidth(vertices);
  if (moduleWidth < 1.0f) {
    throw NotFoundException("Bad module width.");
  }

  int dimension = computeDimension(vertices[12], vertices[14],
                                   vertices[13], vertices[15], moduleWidth);
  if (dimension < 1) {
    throw NotFoundException("Bad dimension.");
  }

  int yDimension = max(computeYDimension(vertices[12], vertices[14],
                                         vertices[13], vertices[15], moduleWidth), dimension);

  // Deskew and sample lines from image.
  Ref<BitMatrix> linesMatrix = sampleLines(vertices, dimension, yDimension);
  Ref<BitMatrix> linesGrid(LinesSampler(linesMatrix, dimension).sample());

  ArrayRef< Ref<ResultPoint> > points(4);
  points[0] = vertices[5];
  points[1] = vertices[4];
  points[2] = vertices[6];
  points[3] = vertices[7];
  return Ref<DetectorResult>(new DetectorResult(linesGrid, points));
}

/**
 * Locate the vertices and the codewords area of a black blob using the Start
 * and Stop patterns as locators.
 *
 * @param matrix the scanned barcode image.
 * @param rowStep the step size for iterating rows (every n-th row).
 * @return an array containing the vertices:
 *           vertices[0] x, y top left barcode
 *           vertices[1] x, y bottom left barcode
 *           vertices[2] x, y top right barcode
 *           vertices[3] x, y bottom right barcode
 *           vertices[4] x, y top left codeword area
 *           vertices[5] x, y bottom left codeword area
 *           vertices[6] x, y top right codeword area
 *           vertices[7] x, y bottom right codeword area
 */
ArrayRef< Ref<ResultPoint> > Detector::findVertices(Ref<BitMatrix> matrix, int rowStep)
{
  const int height = matrix->getHeight();
  const int width = matrix->getWidth();

  ArrayRef< Ref<ResultPoint> > result(16);
  bool found = false;

  ArrayRef<int> counters(new Array<int>(START_PATTERN_LENGTH));

  // Top Left
  for (int i = 0; i < height; i += rowStep) {
    ArrayRef<int> loc = findGuardPattern(matrix, 0, i, width, false, START_PATTERN,
                                         START_PATTERN_LENGTH, counters);
    if (loc) {
      result[0] = new ResultPoint((float)loc[0], (float)i);
      result[4] = new ResultPoint((float)loc[1], (float)i);
      found = true;
      break;
    }
  }
  // Bottom left
  if (found) { // Found the Top Left vertex
    found = false;
    for (int i = height - 1; i > 0; i -= rowStep) {
      ArrayRef<int> loc = findGuardPattern(matrix, 0, i, width, false, START_PATTERN,
                                           START_PATTERN_LENGTH, counters);
      if (loc) {
        result[1] = new ResultPoint((float)loc[0], (float)i);
        result[5] = new ResultPoint((float)loc[1], (float)i);
        found = true;
        break;
      }
    }
  }

  counters = new Array<int>(STOP_PATTERN_LENGTH);

  // Top right
  if (found) { // Found the Bottom Left vertex
    found = false;
    for (int i = 0; i < height; i += rowStep) {
      ArrayRef<int> loc = findGuardPattern(matrix, 0, i, width, false, STOP_PATTERN,
                                           STOP_PATTERN_LENGTH, counters);
      if (loc) {
        result[2] = new ResultPoint((float)loc[1], (float)i);
        result[6] = new ResultPoint((float)loc[0], (float)i);
        found = true;
        break;
      }
    }
  }
  // Bottom right
  if (found) { // Found the Top right vertex
    found = false;
    for (int i = height - 1; i > 0; i -= rowStep) {
      ArrayRef<int> loc = findGuardPattern(matrix, 0, i, width, false, STOP_PATTERN,
                                           STOP_PATTERN_LENGTH, counters);
      if (loc) {
        result[3] = new ResultPoint((float)loc[1], (float)i);
        result[7] = new ResultPoint((float)loc[0], (float)i);
        found = true;
        break;
      }
    }
  }

  return found ? result : ArrayRef< Ref<ResultPoint> >();
}

ArrayRef< Ref<ResultPoint> > Detector::findVertices180(Ref<BitMatrix> matrix, int rowStep) {
  const int height = matrix->getHeight();
  const int width = matrix->getWidth();
  const int halfWidth = width >> 1;

  ArrayRef< Ref<ResultPoint> > result(16);
  bool found = false;

  ArrayRef<int> counters = new Array<int>(START_PATTERN_REVERSE_LENGTH);

  // Top Left
  for (int i = height - 1; i > 0; i -= rowStep) {
    ArrayRef<int> loc =
        findGuardPattern(matrix, halfWidth, i, halfWidth, true, START_PATTERN_REVERSE,
                         START_PATTERN_REVERSE_LENGTH, counters);
    if (loc) {
      result[0] = new ResultPoint((float)loc[1], (float)i);
      result[4] = new ResultPoint((float)loc[0], (float)i);
      found = true;
      break;
    }
  }
  // Bottom Left
  if (found) { // Found the Top Left vertex
    found = false;
    for (int i = 0; i < height; i += rowStep) {
      ArrayRef<int> loc =
          findGuardPattern(matrix, halfWidth, i, halfWidth, true, START_PATTERN_REVERSE,
                           START_PATTERN_REVERSE_LENGTH, counters);
      if (loc) {
        result[1] = new ResultPoint((float)loc[1], (float)i);
        result[5] = new ResultPoint((float)loc[0], (float)i);
        found = true;
        break;
      }
    }
  }

  counters = new Array<int>(STOP_PATTERN_REVERSE_LENGTH);

  // Top Right
  if (found) { // Found the Bottom Left vertex
    found = false;
    for (int i = height - 1; i > 0; i -= rowStep) {
      ArrayRef<int> loc = findGuardPattern(matrix, 0, i, halfWidth, false, STOP_PATTERN_REVERSE,
                                           STOP_PATTERN_REVERSE_LENGTH, counters);
      if (loc) {
        result[2] = new ResultPoint((float)loc[0], (float)i);
        result[6] = new ResultPoint((float)loc[1], (float)i);
        found = true;
        break;
      }
    }
  }
  // Bottom Right
  if (found) { // Found the Top Right vertex
    found = false;
    for (int i = 0; i < height; i += rowStep) {
      ArrayRef<int> loc = findGuardPattern(matrix, 0, i, halfWidth, false, STOP_PATTERN_REVERSE,
                                           STOP_PATTERN_REVERSE_LENGTH, counters);
      if (loc) {
        result[3] = new ResultPoint((float)loc[0], (float)i);
        result[7] = new ResultPoint((float)loc[1], (float)i);
        found = true;
        break;
      }
    }
  }

  return found ? result : ArrayRef< Ref<ResultPoint> >();
}

/**
 * @param matrix row of black/white values to search
 * @param column x position to start search
 * @param row y position to start search
 * @param width the number of pixels to search on this row
 * @param pattern pattern of counts of number of black and white pixels that are
 *                 being searched for as a pattern
 * @param counters array of counters, as long as pattern, to re-use
 * @return start/end horizontal offset of guard pattern, as an array of two ints.
 */
ArrayRef<int> Detector::findGuardPattern(Ref<BitMatrix> matrix,
                                         int column,
                                         int row,
                                         int width,
                                         bool whiteFirst,
                                         const int pattern[],
                                         int patternSize,
                                         ArrayRef<int>& counters) {
  counters->values().assign(counters->size(), 0);
  int patternLength = patternSize;
  bool isWhite = whiteFirst;

  int counterPosition = 0;
  int patternStart = column;
  for (int x = column; x < column + width; x++) {
    bool pixel = matrix->get(x, row);
    if (pixel ^ isWhite) {
      counters[counterPosition]++;
    } else {
      if (counterPosition == patternLength - 1) {
        if (patternMatchVariance(counters, pattern,
                                 MAX_INDIVIDUAL_VARIANCE) < MAX_AVG_VARIANCE) {
          ArrayRef<int> result = new Array<int>(2);
          result[0] = patternStart;
          result[1] = x;
          return result;
        }
        patternStart += counters[0] + counters[1];
        for(int i = 0; i < patternLength - 2; ++i)
          counters[i] = counters[ i + 2];
        counters[patternLength - 2] = 0;
        counters[patternLength - 1] = 0;
        counterPosition--;
      } else {
        counterPosition++;
      }
      counters[counterPosition] = 1;
      isWhite = !isWhite;
    }
  }
  return ArrayRef<int>();
}

/**
 * Determines how closely a set of observed counts of runs of black/white
 * values matches a given target pattern. This is reported as the ratio of
 * the total variance from the expected pattern proportions across all
 * pattern elements, to the length of the pattern.
 *
 * @param counters observed counters
 * @param pattern expected pattern
 * @param maxIndividualVariance The most any counter can differ before we give up
 * @return ratio of total variance between counters and pattern compared to
 *         total pattern size, where the ratio has been multiplied by 256.
 *         So, 0 means no variance (perfect match); 256 means the total
 *         variance between counters and patterns equals the pattern length,
 *         higher values mean even more variance
 */
int Detector::patternMatchVariance(ArrayRef<int>& counters,
                                   const int pattern[],
                                   int maxIndividualVariance)
{
  size_t numCounters = counters->size();
  int total = 0;
  int patternLength = 0;
  for (int i = 0; i < numCounters; i++) {
    total += counters[i];
    patternLength += pattern[i];
  }
  if (total < patternLength) {
    // If we don't even have one pixel per unit of bar width, assume this
    // is too small to reliably match, so fail:
    return numeric_limits<int>::max();
  }
  // We're going to fake floating-point math in integers. We just need to use more bits.
  // Scale up patternLength so that intermediate values below like scaledCounter will have
  // more "significant digits".
  int unitBarWidth = (total << 8) / patternLength;
  maxIndividualVariance = (maxIndividualVariance * unitBarWidth) >> 8;

  int totalVariance = 0;
  for (int x = 0; x < numCounters; x++) {
    int counter = counters[x] << 8;
    int scaledPattern = pattern[x] * unitBarWidth;
    int variance = counter > scaledPattern ? counter - scaledPattern : scaledPattern - counter;
    if (variance > maxIndividualVariance) {
      return numeric_limits<int>::max();
    }
    totalVariance += variance;
  }
  return totalVariance / total;
}

/**
 * <p>Correct the vertices by searching for top and bottom vertices of wide
 * bars, then locate the intersections between the upper and lower horizontal
 * line and the inner vertices vertical lines.</p>
 *
 * @param matrix the scanned barcode image.
 * @param vertices the vertices vector is extended and the new members are:
 *           vertices[ 8] x,y point on upper border of left wide bar
 *           vertices[ 9] x,y point on lower border of left wide bar
 *           vertices[10] x,y point on upper border of right wide bar
 *           vertices[11] x,y point on lower border of right wide bar
 *           vertices[12] x,y final top left codeword area
 *           vertices[13] x,y final bottom left codeword area
 *           vertices[14] x,y final top right codeword area
 *           vertices[15] x,y final bottom right codeword area
 * @param upsideDown true if rotated by 180 degree.
 */
void Detector::correctVertices(Ref<BitMatrix> matrix,
                               ArrayRef< Ref<ResultPoint> >& vertices,
                               bool upsideDown)
{
  bool isLowLeft = abs(vertices[4]->getY() - vertices[5]->getY()) < 20.0;
  bool isLowRight = abs(vertices[6]->getY() - vertices[7]->getY()) < 20.0;
  if (isLowLeft || isLowRight) {
    throw NotFoundException("Cannot find enough PDF417 guard patterns!");
  } else {
    findWideBarTopBottom(matrix, vertices, 0, 0,  8, 17, upsideDown ? 1 : -1);
    findWideBarTopBottom(matrix, vertices, 1, 0,  8, 17, upsideDown ? -1 : 1);
    findWideBarTopBottom(matrix, vertices, 2, 11, 7, 18, upsideDown ? 1 : -1);
    findWideBarTopBottom(matrix, vertices, 3, 11, 7, 18, upsideDown ? -1 : 1);
    findCrossingPoint(vertices, 12, 4, 5, 8, 10, matrix);
    findCrossingPoint(vertices, 13, 4, 5, 9, 11, matrix);
    findCrossingPoint(vertices, 14, 6, 7, 8, 10, matrix);
    findCrossingPoint(vertices, 15, 6, 7, 9, 11, matrix);
  }
}

/**
 * <p>Locate the top or bottom of one of the two wide black bars of a guard pattern.</p>
 *
 * <p>Warning: it only searches along the y axis, so the return points would not be
 * right if the barcode is too curved.</p>
 *
 * @param matrix The bit matrix.
 * @param vertices The 16 vertices located by findVertices(); the result
 *           points are stored into vertices[8], ... , vertices[11].
 * @param offsetVertice The offset of the outer vertice and the inner
 *           vertice (+ 4) to be corrected and (+ 8) where the result is stored.
 * @param startWideBar start of a wide bar.
 * @param lenWideBar length of wide bar.
 * @param lenPattern length of the pattern.
 * @param rowStep +1 if corner should be exceeded towards the bottom, -1 towards the top.
 */
void Detector::findWideBarTopBottom(Ref<BitMatrix> matrix,
                                    ArrayRef< Ref<ResultPoint> > &vertices,
                                    int offsetVertice,
                                    int startWideBar,
                                    int lenWideBar,
                                    int lenPattern,
                                    int rowStep)
{
  Ref<ResultPoint> verticeStart(vertices[offsetVertice]);
  Ref<ResultPoint> verticeEnd(vertices[offsetVertice + 4]);

  // Start horizontally at the middle of the bar.
  int endWideBar = startWideBar + lenWideBar;
  float barDiff = verticeEnd->getX() - verticeStart->getX();
  float barStart = verticeStart->getX() + barDiff * (float)startWideBar / (float)lenPattern;
  float barEnd = verticeStart->getX() + barDiff * (float)endWideBar / (float)lenPattern;
  int x = common::detector::Math::round((barStart + barEnd) / 2.0f);

  // Start vertically between the preliminary vertices.
  int yStart = common::detector::Math::round(verticeStart->getY());
  int y = yStart;

  // Find offset of thin bar to the right as additional safeguard.
  int nextBarX = int(max(barStart, barEnd) + 1);
  for (; nextBarX < matrix->getWidth(); nextBarX++)
    if (!matrix->get(nextBarX - 1, y) && matrix->get(nextBarX, y)) break;
  nextBarX -= x;

  bool isEnd = false;
  while (!isEnd) {
    if (matrix->get(x, y)) {
      // If the thin bar to the right ended, stop as well
      isEnd = !matrix->get(x + nextBarX, y) && !matrix->get(x + nextBarX + 1, y);
      y += rowStep;
      if (y <= 0 || y >= (int)matrix->getHeight() - 1) {
        // End of barcode image reached.
        isEnd = true;
      }
    } else {
      // Look sidewise whether black bar continues? (in the case the image is skewed)
      if (x > 0 && matrix->get(x - 1, y)) {
        x--;
      } else if (x < (int)matrix->getWidth() - 1 && matrix->get(x + 1, y)) {
        x++;
      } else {
        // End of pattern regarding big bar and big gap reached.
        isEnd = true;
        if (y != yStart) {
          // Turn back one step, because target has been exceeded.
          y -= rowStep;
        }
      }
    }
  }

  vertices[offsetVertice + 8] = new ResultPoint((float)x, (float)y);
}

/**
 * <p>Finds the intersection of two lines.</p>
 *
 * @param vertices The reference of the vertices vector
 * @param idxResult Index of result point inside the vertices vector.
 * @param idxLineA1
 * @param idxLineA2 Indices two points inside the vertices vector that define the first line.
 * @param idxLineB1
 * @param idxLineB2 Indices two points inside the vertices vector that define the second line.
 * @param matrix: bit matrix, here only for testing whether the result is inside the matrix.
 * @return Returns true when the result is valid and lies inside the matrix. Otherwise throws an
 * exception.
 **/
void Detector::findCrossingPoint(ArrayRef< Ref<ResultPoint> >& vertices,
                                 int idxResult,
                                 int idxLineA1, int idxLineA2,
                                 int idxLineB1, int idxLineB2,
                                 Ref<BitMatrix>& matrix)
{
  Point p1(vertices[idxLineA1]->getX(), vertices[idxLineA1]->getY());
  Point p2(vertices[idxLineA2]->getX(), vertices[idxLineA2]->getY());
  Point p3(vertices[idxLineB1]->getX(), vertices[idxLineB1]->getY());
  Point p4(vertices[idxLineB2]->getX(), vertices[idxLineB2]->getY());

  Point result(intersection(Line(p1, p2), Line(p3, p4)));
  if (result.x == numeric_limits<float>::infinity() ||
      result.y == numeric_limits<float>::infinity()) {
    throw NotFoundException("PDF:Detector: cannot find the crossing of parallel lines!");
  }

  int x = common::detector::Math::round(result.x);
  int y = common::detector::Math::round(result.y);
  if (x < 0 || x >= (int)matrix->getWidth() || y < 0 || y >= (int)matrix->getHeight()) {
    throw NotFoundException("PDF:Detector: crossing points out of region!");
  }

  vertices[idxResult] = Ref<ResultPoint>(new ResultPoint(result.x, result.y));
}

/**
 * Computes the intersection between two lines.
 */
Point Detector::intersection(Line a, Line b) {
  float dxa = a.start.x - a.end.x;
  float dxb = b.start.x - b.end.x;
  float dya = a.start.y - a.end.y;
  float dyb = b.start.y - b.end.y;

  float p = a.start.x * a.end.y - a.start.y * a.end.x;
  float q = b.start.x * b.end.y - b.start.y * b.end.x;
  float denom = dxa * dyb - dya * dxb;
  if(abs(denom) < 1e-12)  // Lines don't intersect (replaces "denom == 0")
    return Point(numeric_limits<float>::infinity(),
                 numeric_limits<float>::infinity());

  float x = (p * dxb - dxa * q) / denom;
  float y = (p * dyb - dya * q) / denom;

  return Point(x, y);
}

/**
 * <p>Estimates module size (pixels in a module) based on the Start and End
 * finder patterns.</p>
 *
 * @param vertices an array of vertices:
 *           vertices[0] x, y top left barcode
 *           vertices[1] x, y bottom left barcode
 *           vertices[2] x, y top right barcode
 *           vertices[3] x, y bottom right barcode
 *           vertices[4] x, y top left codeword area
 *           vertices[5] x, y bottom left codeword area
 *           vertices[6] x, y top right codeword area
 *           vertices[7] x, y bottom right codeword area
 * @return the module size.
 */
float Detector::computeModuleWidth(ArrayRef< Ref<ResultPoint> >& vertices) {
  float pixels1 = ResultPoint::distance(vertices[0], vertices[4]);
  float pixels2 = ResultPoint::distance(vertices[1], vertices[5]);
  float moduleWidth1 = (pixels1 + pixels2) / (17 * 2.0f);
  float pixels3 = ResultPoint::distance(vertices[6], vertices[2]);
  float pixels4 = ResultPoint::distance(vertices[7], vertices[3]);
  float moduleWidth2 = (pixels3 + pixels4) / (18 * 2.0f);
  return (moduleWidth1 + moduleWidth2) / 2.0f;
}

/**
 * Computes the dimension (number of modules in a row) of the PDF417 Code
 * based on vertices of the codeword area and estimated module size.
 *
 * @param topLeft     of codeword area
 * @param topRight    of codeword area
 * @param bottomLeft  of codeword area
 * @param bottomRight of codeword are
 * @param moduleWidth estimated module size
 * @return the number of modules in a row.
 */
int Detector::computeDimension(Ref<ResultPoint> const& topLeft,
                               Ref<ResultPoint> const& topRight,
                               Ref<ResultPoint> const& bottomLeft,
                               Ref<ResultPoint> const& bottomRight,
                               float moduleWidth)
{
  int topRowDimension = MathUtils::round(ResultPoint::distance(topLeft, topRight) / moduleWidth);
  int bottomRowDimension =
      MathUtils::round(ResultPoint::distance(bottomLeft, bottomRight) / moduleWidth);
  return ((((topRowDimension + bottomRowDimension) >> 1) + 8) / 17) * 17;
}

/**
 * Computes the y dimension (number of modules in a column) of the PDF417 Code
 * based on vertices of the codeword area and estimated module size.
 *
 * @param topLeft     of codeword area
 * @param topRight    of codeword area
 * @param bottomLeft  of codeword area
 * @param bottomRight of codeword are
 * @param moduleWidth estimated module size
 * @return the number of modules in a row.
 */
int Detector::computeYDimension(Ref<ResultPoint> const& topLeft,
                                Ref<ResultPoint> const& topRight,
                                Ref<ResultPoint> const& bottomLeft,
                                Ref<ResultPoint> const& bottomRight,
                                float moduleWidth)
{
  int leftColumnDimension =
      MathUtils::round(ResultPoint::distance(topLeft, bottomLeft) / moduleWidth);
  int rightColumnDimension =
      MathUtils::round(ResultPoint::distance(topRight, bottomRight) / moduleWidth);
  return (leftColumnDimension + rightColumnDimension) >> 1;
}

/**
 * Deskew and over-sample image.
 *
 * @param vertices vertices from findVertices()
 * @param dimension x dimension
 * @param yDimension y dimension
 * @return an over-sampled BitMatrix.
 */
Ref<BitMatrix> Detector::sampleLines(ArrayRef< Ref<ResultPoint> > const& vertices,
                                     int dimensionY,
                                     int dimension) {
  const int sampleDimensionX = dimension * 8;
  const int sampleDimensionY = dimensionY * 4;
  Ref<PerspectiveTransform> transform(
      PerspectiveTransform::quadrilateralToQuadrilateral(
          0.0f, 0.0f,
          (float)sampleDimensionX, 0.0f,
          0.0f, (float)sampleDimensionY,
          (float)sampleDimensionX, (float)sampleDimensionY,
          vertices[12]->getX(), vertices[12]->getY(),
          vertices[14]->getX(), vertices[14]->getY(),
          vertices[13]->getX(), vertices[13]->getY(),
          vertices[15]->getX(), vertices[15]->getY()));

  Ref<BitMatrix> linesMatrix = GridSampler::getInstance().sampleGrid(
      image_->getBlackMatrix(), sampleDimensionX, sampleDimensionY, transform);


  return linesMatrix;
}
}
}
}

// file: zxing/pdf417/detector/LinesSampler.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 * Copyright 2010, 2012 ZXing authors All rights reserved.
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
// #include <zxing/pdf417/detector/LinesSampler.h>
// #include <zxing/pdf417/decoder/BitMatrixParser.h>
// #include <zxing/NotFoundException.h>
// #include <zxing/common/Point.h>
// #include <algorithm>  // vs12, std::min und std:max
// #include <cmath>

namespace zxing {
namespace pdf417 {
namespace detector {
            
            
const int LinesSampler::MODULES_IN_SYMBOL;
const int LinesSampler::BARS_IN_SYMBOL;
const int LinesSampler::POSSIBLE_SYMBOLS;
const int LinesSampler::BARCODE_START_OFFSET;

namespace {

class VoteResult {
 private:
  bool indecisive;
  int vote;
 public:
  VoteResult() : indecisive(false), vote(0) {}
  bool isIndecisive() {
    return indecisive;
  }
  void setIndecisive(bool indecisive) {
    this->indecisive = indecisive;
  }
  int getVote() {
    return vote;
  }
  void setVote(int vote) {
    this->vote = vote;
  }
};

VoteResult getValueWithMaxVotes(map<int, int>& votes) {
  VoteResult result;
  int maxVotes = 0;
  for (map<int, int>::iterator i = votes.begin(); i != votes.end(); i++) {
    if (i->second > maxVotes) {
      maxVotes = i->second;
      result.setVote(i->first);
      result.setIndecisive(false);
    } else if (i->second == maxVotes) {
      result.setIndecisive(true);
    }
  }
  return result;
}

}

vector<float> LinesSampler::init_ratios_table() {
  // Pre-computes and outputs the symbol ratio table.
    vector<vector<float> > table (decoder::BitMatrixParser::SYMBOL_TABLE_LENGTH);
  for(int i=0; i < (int)table.size(); ++i) {
    table[i].resize(LinesSampler::BARS_IN_SYMBOL);
  }
  vector<float> RATIOS_TABLE (decoder::BitMatrixParser::SYMBOL_TABLE_LENGTH * LinesSampler::BARS_IN_SYMBOL);
  int x = 0;
  for (int i = 0; i < decoder::BitMatrixParser::SYMBOL_TABLE_LENGTH; i++) {
    int currentSymbol = decoder::BitMatrixParser::SYMBOL_TABLE[i];
    int currentBit = currentSymbol & 0x1;
    for (int j = 0; j < BARS_IN_SYMBOL; j++) {
      float size = 0.0f;
      while ((currentSymbol & 0x1) == currentBit) {
        size += 1.0f;
        currentSymbol >>= 1;
      }
      currentBit = currentSymbol & 0x1;
      table[i][BARS_IN_SYMBOL - j - 1] = size / MODULES_IN_SYMBOL;
    }
    for (int j = 0; j < BARS_IN_SYMBOL; j++) {
      RATIOS_TABLE[x] = table[i][j];
      x++;
    }
  }
  return RATIOS_TABLE;
}

const vector<float> LinesSampler::RATIOS_TABLE = init_ratios_table();

LinesSampler::LinesSampler(Ref<BitMatrix> linesMatrix, int dimension)
    : linesMatrix_(linesMatrix), dimension_(dimension) {}

/**
 * Samples a grid from a lines matrix.
 *
 * @return the potentially decodable bit matrix.
 */
Ref<BitMatrix> LinesSampler::sample() {
  const int symbolsPerLine = dimension_ / MODULES_IN_SYMBOL;

  // XXX
  vector<float> symbolWidths;
  computeSymbolWidths(symbolWidths, symbolsPerLine, linesMatrix_);

  // XXX
  vector<vector<int> > codewords(linesMatrix_->getHeight());
  vector<vector<int> > clusterNumbers(linesMatrix_->getHeight());
  linesMatrixToCodewords(clusterNumbers, symbolsPerLine, symbolWidths, linesMatrix_, codewords);

  // XXX
  vector<vector<map<int, int> > > votes =
      distributeVotes(symbolsPerLine, codewords, clusterNumbers);

  // XXX
  vector<vector<int> > detectedCodeWords(votes.size());
  for (int i = 0; i < (int)votes.size(); i++) {
    detectedCodeWords[i].resize(votes[i].size(), 0);
    for (int j = 0; j < (int)votes[i].size(); j++) {
      if (!votes[i][j].empty()) {
        detectedCodeWords[i][j] = getValueWithMaxVotes(votes[i][j]).getVote();
      }
    }
  }

  // XXX
  vector<int> insertLinesAt = findMissingLines(symbolsPerLine, detectedCodeWords);

  // XXX
  int rowCount = decodeRowCount(symbolsPerLine, detectedCodeWords, insertLinesAt);
  detectedCodeWords.resize(rowCount);

  // XXX
  Ref<BitMatrix> grid(new BitMatrix(dimension_, (int)detectedCodeWords.size()));
  codewordsToBitMatrix(detectedCodeWords, grid);

  return grid;
}

/**
 * @brief LinesSampler::codewordsToBitMatrix
 * @param codewords
 * @param matrix
 */
void LinesSampler::codewordsToBitMatrix(vector<vector<int> > &codewords, Ref<BitMatrix> &matrix) {
  for (int i = 0; i < (int)codewords.size(); i++) {
    for (int j = 0; j < (int)codewords[i].size(); j++) {
      int moduleOffset = j * MODULES_IN_SYMBOL;
      for (int k = 0; k < MODULES_IN_SYMBOL; k++) {
        if ((codewords[i][j] & (1 << (MODULES_IN_SYMBOL - k - 1))) > 0) {
          matrix->set(moduleOffset + k, i);
        }
      }
    }
  }
}

/**
 * @brief LinesSampler::calculateClusterNumber
 * @param codeword
 * @return
 */
int LinesSampler::calculateClusterNumber(int codeword) {
  if (codeword == 0) {
    return -1;
  }
  int barNumber = 0;
  bool blackBar = true;
  int clusterNumber = 0;
  for (int i = 0; i < MODULES_IN_SYMBOL; i++) {
    if ((codeword & (1 << i)) > 0) {
      if (!blackBar) {
        blackBar = true;
        barNumber++;
      }
      if (barNumber % 2 == 0) {
        clusterNumber++;
      } else {
        clusterNumber--;
      }
    } else {
      if (blackBar) {
        blackBar = false;
      }
    }
  }
  return (clusterNumber + 9) % 9;
}

//#define OUTPUT_SYMBOL_WIDTH 1
//#define OUTPUT_BAR_WIDTH 1
//#define OUTPUT_CW_STARTS 1
//#define OUTPUT_CLUSTER_NUMBERS 1
//#define OUTPUT_EC_LEVEL 1

void LinesSampler::computeSymbolWidths(vector<float> &symbolWidths, const int symbolsPerLine, Ref<BitMatrix> linesMatrix)
{
  int symbolStart = 0;
  bool lastWasSymbolStart = true;
  const float symbolWidth = symbolsPerLine > 0 ? (float)linesMatrix->getWidth() / (float)symbolsPerLine : (float)linesMatrix->getWidth();

  // Use the following property of PDF417 barcodes to detect symbols:
  // Every symbol starts with a black module and every symbol is 17 modules wide,
  // therefore there have to be columns in the line matrix that are completely composed of black pixels.
  vector<int> blackCount(linesMatrix->getWidth(), 0);
  for (int x = BARCODE_START_OFFSET; x < linesMatrix->getWidth(); x++) {
    for (int y = 0; y < linesMatrix->getHeight(); y++) {
      if (linesMatrix->get(x, y)) {
        blackCount[x]++;
      }
    }
    if (blackCount[x] == linesMatrix->getHeight()) {
      if (!lastWasSymbolStart) {
        float currentWidth = (float)(x - symbolStart);
        // Make sure we really found a symbol by asserting a minimal size of 75% of the expected symbol width.
        // This might break highly distorted barcodes, but fixes an issue with barcodes where there is a
        // full black column from top to bottom within a symbol.
        if (currentWidth > 0.75 * symbolWidth) {
          // The actual symbol width might be slightly bigger than the expected symbol width,
          // but if we are more than half an expected symbol width bigger, we assume that
          // we missed one or more symbols and assume that they were the expected symbol width.
          while (currentWidth > 1.5 * symbolWidth) {
            symbolWidths.push_back(symbolWidth);
            currentWidth -= symbolWidth;
          }
          symbolWidths.push_back(currentWidth);
          lastWasSymbolStart = true;
          symbolStart = x;
        }
      }
    } else {
      if (lastWasSymbolStart) {
        lastWasSymbolStart = false;
      }
    }
  }

  // The last symbol ends at the right edge of the matrix, where there usually is no black bar.
  float currentWidth = (float)(linesMatrix->getWidth() - symbolStart);
  while (currentWidth > 1.5 * symbolWidth) {
    symbolWidths.push_back(symbolWidth);
    currentWidth -= symbolWidth;
  }
  symbolWidths.push_back(currentWidth);


#if PDF417_DIAG && OUTPUT_SYMBOL_WIDTH
  {
    cout << "symbols per line: " << symbolsPerLine << endl;
    cout << "symbol width (" << symbolWidths.size() << "): ";
    for (int i = 0; i < symbolWidths.size(); i++) {
      cout << symbolWidths[i] << ", ";
    }
    cout << endl;
  }
#endif
}

void LinesSampler::linesMatrixToCodewords(vector<vector<int> >& clusterNumbers,
                                          const int symbolsPerLine,
                                          const vector<float>& symbolWidths,
                                          Ref<BitMatrix> linesMatrix,
                                          vector<vector<int> >& codewords)
{
  for (int y = 0; y < linesMatrix->getHeight(); y++) {
    // Not sure if this is the right way to handle this but avoids an error:
    if (symbolsPerLine > (int)symbolWidths.size()) {
      throw NotFoundException("Inconsistent number of symbols in this line.");
    }

    // TODO: use symbolWidths.size() instead of symbolsPerLine to at least decode some codewords

    codewords[y].resize(symbolsPerLine, 0);
    clusterNumbers[y].resize(symbolsPerLine, -1);
    int line = y;
    vector<int> barWidths(1, 0);
    int barCount = 0;
    // Runlength encode the bars in the scanned linesMatrix.
    // We assume that the first bar is black, as determined by the PDF417 standard.
    bool isSetBar = true;
    // Filter small white bars at the beginning of the barcode.
    // Small white bars may occur due to small deviations in scan line sampling.
    barWidths[0] += BARCODE_START_OFFSET;
    for (int x = BARCODE_START_OFFSET; x < linesMatrix->getWidth(); x++) {
      if (linesMatrix->get(x, line)) {
        if (!isSetBar) {
          isSetBar = true;
          barCount++;
          barWidths.resize(barWidths.size() + 1);
        }
      } else {
        if (isSetBar) {
          isSetBar = false;
          barCount++;
          barWidths.resize(barWidths.size() + 1);
        }

      }
      barWidths[barCount]++;
    }
    // Don't forget the last bar.
    barCount++;
    barWidths.resize(barWidths.size() + 1);

#if PDF417_DIAG && OUTPUT_BAR_WIDTH
    {
      for (int i = 0; i < barWidths.size(); i++) {
        cout << barWidths[i] << ", ";
      }
      cout << endl;
    }
#endif

    //////////////////////////////////////////////////

    // Find the symbols in the line by counting bar lengths until we reach symbolWidth.
    // We make sure, that the last bar of a symbol is always white, as determined by the PDF417 standard.
    // This helps to reduce the amount of errors done during the symbol recognition.
    // The symbolWidth usually is not constant over the width of the barcode.
    int cwWidth = 0;
    int cwCount = 0;
    vector<int> cwStarts(symbolsPerLine, 0);
    cwStarts[0] = 0;
    cwCount++;
    for (int i = 0; i < barCount && cwCount < symbolsPerLine; i++) {
      cwWidth += barWidths[i];
      if ((float)cwWidth > symbolWidths[cwCount - 1]) {
        if ((i % 2) == 1) { // check if bar is white
          i++;
        }
        cwWidth = barWidths[i];
        cwStarts[cwCount] = i;
        cwCount++;
      }
    }

#if PDF417_DIAG && OUTPUT_CW_STARTS
    {
      for (int i = 0; i < cwStarts.size(); i++) {
        cout << cwStarts[i] << ", ";
      }
      cout << endl;
    }
#endif

    ///////////////////////////////////////////

    vector<vector<float> > cwRatios(symbolsPerLine);
    // Distribute bar widths to modules of a codeword.
    for (int i = 0; i < symbolsPerLine; i++) {
      cwRatios[i].resize(BARS_IN_SYMBOL, 0.0f);
      const int cwStart = cwStarts[i];
      const int cwEnd = (i == symbolsPerLine - 1) ? barCount : cwStarts[i + 1];
      const int cwLength = cwEnd - cwStart;

      if (cwLength < 7 || cwLength > 9) {
        // We try to recover smybols with 7 or 9 bars and spaces with heuristics, but everything else is beyond repair.
        continue;
      }

      float cwWidth = 0;

      // For symbols with 9 bar length simply ignore the last bar.
      for (int j = 0; j < min(BARS_IN_SYMBOL, cwLength); ++j) {
        cwWidth += (float)barWidths[cwStart + j];
      }

      // If there were only 7 bars and spaces detected use the following heuristic:
      // Assume the length of the symbol is symbolWidth and the last (unrecognized) bar uses all remaining space.
      if (cwLength == 7) {
        for (int j = 0; j < cwLength; ++j) {
          cwRatios[i][j] = (float)barWidths[cwStart + j] / symbolWidths[i];
        }
        cwRatios[i][7] = (symbolWidths[i] - cwWidth) / symbolWidths[i];
      } else {
        for (int j = 0; j < (int)cwRatios[i].size(); ++j) {
          cwRatios[i][j] = (float)barWidths[cwStart + j] / cwWidth;
        }
      }

      float bestMatchError = std::numeric_limits<float>::max();
      int bestMatch = 0;

      // Search for the most possible codeword by comparing the ratios of bar size to symbol width.
      // The sum of the squared differences is used as similarity metric.
      // (Picture it as the square euclidian distance in the space of eight tuples where a tuple represents the bar ratios.)
      for (int j = 0; j < POSSIBLE_SYMBOLS; j++) {
        float error = 0.0f;
        for (int k = 0; k < BARS_IN_SYMBOL; k++) {
          float diff = RATIOS_TABLE[j * BARS_IN_SYMBOL + k] - cwRatios[i][k];
          error += diff * diff;
          if (error >= bestMatchError) {
            break;
          }
        }
        if (error < bestMatchError) {
          bestMatchError = error;
          bestMatch = decoder::BitMatrixParser::SYMBOL_TABLE[j];
        }
      }
      codewords[y][i] = bestMatch;
      clusterNumbers[y][i] = calculateClusterNumber(bestMatch);
    }
  }


#if PDF417_DIAG && OUTPUT_CLUSTER_NUMBERS
  {
    for (int i = 0; i < clusterNumbers.size(); i++) {
      for (int j = 0; j < clusterNumbers[i].size(); j++) {
        cout << clusterNumbers[i][j] << ", ";
      }
      cout << endl;
    }
  }
#endif


#if PDF417_DIAG
  {
    Ref<BitMatrix> bits(new BitMatrix(symbolsPerLine * MODULES_IN_SYMBOL, codewords.size()));
    codewordsToBitMatrix(codewords, bits);
    static int __cnt__ = 0;
    stringstream ss;
    ss << "pdf417-detectedRaw" << __cnt__++ << ".png";
    bits->writePng(ss.str().c_str(), 8, 16);
  }
#endif
}

vector<vector<map<int,  int> > >
LinesSampler::distributeVotes(const int symbolsPerLine,
                              const vector<vector<int> >& codewords,
                              const vector<vector<int> >& clusterNumbers)
{
  // Matrix of votes for codewords which are possible at this position.
  vector<vector<map<int, int> > > votes(1);
  votes[0].resize(symbolsPerLine);

  int currentRow = 0;
  map<int, int> clusterNumberVotes;
  int lastLineClusterNumber = -1;

  for (int y = 0; y < (int)codewords.size(); y++) {
    // Vote for the most probable cluster number for this row.
    clusterNumberVotes.clear();
    for (int i = 0; i < (int)codewords[y].size(); i++) {
      if (clusterNumbers[y][i] != -1) {
        clusterNumberVotes[clusterNumbers[y][i]] = clusterNumberVotes[clusterNumbers[y][i]] + 1;
      }
    }

    // Ignore lines where no codeword could be read.
    if (!clusterNumberVotes.empty()) {
      VoteResult voteResult = getValueWithMaxVotes(clusterNumberVotes);
      bool lineClusterNumberIsIndecisive = voteResult.isIndecisive();
      int lineClusterNumber = voteResult.getVote();

      // If there are to few votes on the lines cluster number, we keep the old one.
      // This avoids switching lines because of damaged inter line readings, but
      // may cause problems for barcodes with four or less rows.
      if (lineClusterNumberIsIndecisive) {
        lineClusterNumber = lastLineClusterNumber;
      }

      if ((lineClusterNumber != ((lastLineClusterNumber + 3) % 9)) && (lastLineClusterNumber != -1)) {
        lineClusterNumber = lastLineClusterNumber;
      }

      // Ignore broken lines at the beginning of the barcode.
      if ((lineClusterNumber == 0 && lastLineClusterNumber == -1) || (lastLineClusterNumber != -1)) {
        if ((lineClusterNumber == ((lastLineClusterNumber + 3) % 9)) && (lastLineClusterNumber != -1)) {
          currentRow++;
          if ((int)votes.size() < currentRow + 1) {
            votes.resize(currentRow + 1);
            votes[currentRow].resize(symbolsPerLine);
          }
        }

        if ((lineClusterNumber == ((lastLineClusterNumber + 6) % 9)) && (lastLineClusterNumber != -1)) {
          currentRow += 2;
          if ((int)votes.size() < currentRow + 1) {
            votes.resize(currentRow + 1);
            votes[currentRow].resize(symbolsPerLine);
          }
        }

        for (int i = 0; i < (int)codewords[y].size(); i++) {
          if (clusterNumbers[y][i] != -1) {
            if (clusterNumbers[y][i] == lineClusterNumber) {
              votes[currentRow][i][codewords[y][i]] = votes[currentRow][i][codewords[y][i]] + 1;
            } else if (clusterNumbers[y][i] == ((lineClusterNumber + 3) % 9)) {
              if ((int)votes.size() < currentRow + 2) {
                votes.resize(currentRow + 2);
                votes[currentRow + 1].resize(symbolsPerLine);
              }
              votes[currentRow + 1][i][codewords[y][i]] = votes[currentRow + 1][i][codewords[y][i]] + 1;
            } else if ((clusterNumbers[y][i] == ((lineClusterNumber + 6) % 9)) && (currentRow > 0)) {
              votes[currentRow - 1][i][codewords[y][i]] = votes[currentRow - 1][i][codewords[y][i]] + 1;
            }
          }
        }
        lastLineClusterNumber = lineClusterNumber;
      }
    }
  }

  return votes;
}


vector<int>
LinesSampler::findMissingLines(const int symbolsPerLine, vector<vector<int> > &detectedCodeWords) {
  vector<int> insertLinesAt;
  if (detectedCodeWords.size() > 1) {
    for (int i = 0; i < (int)detectedCodeWords.size() - 1; i++) {
      int clusterNumberRow = -1;
      for (int j = 0; j < (int)detectedCodeWords[i].size() && clusterNumberRow == -1; j++) {
        int clusterNumber = calculateClusterNumber(detectedCodeWords[i][j]);
        if (clusterNumber != -1) {
          clusterNumberRow = clusterNumber;
        }
      }
      if (i == 0) {
        // The first line must have the cluster number 0. Insert empty lines to match this.
        if (clusterNumberRow > 0) {
          insertLinesAt.push_back(0);
          if (clusterNumberRow > 3) {
            insertLinesAt.push_back(0);
          }
        }
      }
      int clusterNumberNextRow = -1;
      for (int j = 0; j < (int)detectedCodeWords[i + 1].size() && clusterNumberNextRow == -1; j++) {
        int clusterNumber = calculateClusterNumber(detectedCodeWords[i + 1][j]);
        if (clusterNumber != -1) {
          clusterNumberNextRow = clusterNumber;
        }
      }
      if ((clusterNumberRow + 3) % 9 != clusterNumberNextRow
          && clusterNumberRow != -1
          && clusterNumberNextRow != -1) {
        // The cluster numbers are not consecutive. Insert an empty line between them.
        insertLinesAt.push_back(i + 1);
        if (clusterNumberRow == clusterNumberNextRow) {
          // There may be two lines missing. This is detected when two consecutive lines have the same cluster number.
          insertLinesAt.push_back(i + 1);
        }
      }
    }
  }

  for (int i = 0; i < (int)insertLinesAt.size(); i++) {
    detectedCodeWords.insert(detectedCodeWords.begin() + insertLinesAt[i] + i, vector<int>(symbolsPerLine, 0));
  }

  return insertLinesAt;
}

int LinesSampler::decodeRowCount(const int symbolsPerLine, vector<vector<int> > &detectedCodeWords, vector<int> &insertLinesAt)
{
  // Use the information in the first and last column to determin the number of rows and find more missing rows.
  // For missing rows insert blank space, so the error correction can try to fill them in.

  map<int, int> rowCountVotes;
  map<int, int> ecLevelVotes;
  map<int, int> rowNumberVotes;
  int lastRowNumber = -1;
  insertLinesAt.clear();

  for (int i = 0; i + 2 < (int)detectedCodeWords.size(); i += 3) {
    rowNumberVotes.clear();
    int firstCodewordDecodedLeft = -1;
    int secondCodewordDecodedLeft = -1;
    int thirdCodewordDecodedLeft = -1;
    int firstCodewordDecodedRight = -1;
    int secondCodewordDecodedRight = -1;
    int thirdCodewordDecodedRight = -1;

    if (detectedCodeWords[i][0] != 0) {
      firstCodewordDecodedLeft = decoder::BitMatrixParser::getCodeword(detectedCodeWords[i][0]);
    }
    if (detectedCodeWords[i + 1][0] != 0) {
      secondCodewordDecodedLeft = decoder::BitMatrixParser::getCodeword(detectedCodeWords[i + 1][0]);
    }
    if (detectedCodeWords[i + 2][0] != 0) {
      thirdCodewordDecodedLeft = decoder::BitMatrixParser::getCodeword(detectedCodeWords[i + 2][0]);
    }

    if (detectedCodeWords[i][detectedCodeWords[i].size() - 1] != 0) {
      firstCodewordDecodedRight = decoder::BitMatrixParser::getCodeword(detectedCodeWords[i][detectedCodeWords[i].size() - 1]);
    }
    if (detectedCodeWords[i + 1][detectedCodeWords[i + 1].size() - 1] != 0) {
      secondCodewordDecodedRight = decoder::BitMatrixParser::getCodeword(detectedCodeWords[i + 1][detectedCodeWords[i + 1].size() - 1]);
    }
    if (detectedCodeWords[i + 2][detectedCodeWords[i + 2].size() - 1] != 0) {
      thirdCodewordDecodedRight = decoder::BitMatrixParser::getCodeword(detectedCodeWords[i + 2][detectedCodeWords[i + 2].size() - 1]);
    }

    if (firstCodewordDecodedLeft != -1 && secondCodewordDecodedLeft != -1) {
      int leftRowCount = ((firstCodewordDecodedLeft % 30) * 3) + ((secondCodewordDecodedLeft % 30) % 3);
      int leftECLevel = (secondCodewordDecodedLeft % 30) / 3;

      rowCountVotes[leftRowCount] = rowCountVotes[leftRowCount] + 1;
      ecLevelVotes[leftECLevel] = ecLevelVotes[leftECLevel] + 1;
    }

    if (secondCodewordDecodedRight != -1 && thirdCodewordDecodedRight != -1) {
      int rightRowCount = ((secondCodewordDecodedRight % 30) * 3) + ((thirdCodewordDecodedRight % 30) % 3);
      int rightECLevel = (thirdCodewordDecodedRight % 30) / 3;

      rowCountVotes[rightRowCount] = rowCountVotes[rightRowCount] + 1;
      ecLevelVotes[rightECLevel] = ecLevelVotes[rightECLevel] + 1;
    }

    if (firstCodewordDecodedLeft != -1) {
      int rowNumber = firstCodewordDecodedLeft / 30;
      rowNumberVotes[rowNumber] = rowNumberVotes[rowNumber] + 1;
    }
    if (secondCodewordDecodedLeft != -1) {
      int rowNumber = secondCodewordDecodedLeft / 30;
      rowNumberVotes[rowNumber] = rowNumberVotes[rowNumber] + 1;
    }
    if (thirdCodewordDecodedLeft != -1) {
      int rowNumber = thirdCodewordDecodedLeft / 30;
      rowNumberVotes[rowNumber] = rowNumberVotes[rowNumber] + 1;
    }
    if (firstCodewordDecodedRight != -1) {
      int rowNumber = firstCodewordDecodedRight / 30;
      rowNumberVotes[rowNumber] = rowNumberVotes[rowNumber] + 1;
    }
    if (secondCodewordDecodedRight != -1) {
      int rowNumber = secondCodewordDecodedRight / 30;
      rowNumberVotes[rowNumber] = rowNumberVotes[rowNumber] + 1;
    }
    if (thirdCodewordDecodedRight != -1) {
      int rowNumber = thirdCodewordDecodedRight / 30;
      rowNumberVotes[rowNumber] = rowNumberVotes[rowNumber] + 1;
    }
    int rowNumber = getValueWithMaxVotes(rowNumberVotes).getVote();
    if (lastRowNumber + 1 < rowNumber) {
      for (int j = lastRowNumber + 1; j < rowNumber; j++) {
        insertLinesAt.push_back(i);
        insertLinesAt.push_back(i);
        insertLinesAt.push_back(i);
      }
    }
    lastRowNumber = rowNumber;
  }

  for (int i = 0; i < (int)insertLinesAt.size(); i++) {
    detectedCodeWords.insert(detectedCodeWords.begin() + insertLinesAt[i] + i, vector<int>(symbolsPerLine, 0));
  }

  int rowCount = getValueWithMaxVotes(rowCountVotes).getVote();
  // int ecLevel = getValueWithMaxVotes(ecLevelVotes);

#if PDF417_DIAG && OUTPUT_EC_LEVEL
  {
    cout << "EC Level: " << ecLevel << " (" << ((1 << (ecLevel + 1)) - 2) << " EC Codewords)" << endl;
  }
#endif
  rowCount += 1;
  return rowCount;
}

/**
 * Ends up being a bit faster than Math.round(). This merely rounds its
 * argument to the nearest int, where x.5 rounds up.
 */
int LinesSampler::round(float d)
{
  return (int)(d + 0.5f);
}

Point LinesSampler::intersection(Line a, Line b) {
  float dxa = a.start.x - a.end.x;
  float dxb = b.start.x - b.end.x;
  float dya = a.start.y - a.end.y;
  float dyb = b.start.y - b.end.y;

  float p = a.start.x * a.end.y - a.start.y * a.end.x;
  float q = b.start.x * b.end.y - b.start.y * b.end.x;
  float denom = dxa * dyb - dya * dxb;
  if(abs(denom) < 1e-12)  // Lines don't intersect (replaces "denom == 0")
    return Point(std::numeric_limits<float>::infinity(),
                 std::numeric_limits<float>::infinity());

  float x = (p * dxb - dxa * q) / denom;
  float y = (p * dyb - dya * q) / denom;

  return Point(x, y);
}
}
}
}

// file: zxing/qrcode/ErrorCorrectionLevel.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  ErrorCorrectionLevel.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 15/05/2008.
 *  Copyright 2008-2011 ZXing authors All rights reserved.
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

using std::string;

namespace zxing {
namespace qrcode {

ErrorCorrectionLevel::ErrorCorrectionLevel(int inOrdinal,
                                           int bits,
                                           char const* name) :
  ordinal_(inOrdinal), bits_(bits), name_(name) {}

int ErrorCorrectionLevel::ordinal() const {
  return ordinal_;
}

int ErrorCorrectionLevel::bits() const {
  return bits_;
}

string const& ErrorCorrectionLevel::name() const {
  return name_;
}

ErrorCorrectionLevel::operator string const& () const {
  return name_;
}

ErrorCorrectionLevel& ErrorCorrectionLevel::forBits(int bits) {
  if (bits < 0 || bits >= N_LEVELS) {
    throw ReaderException("Ellegal error correction level bits");
  }
  return *FOR_BITS[bits];
}

  ErrorCorrectionLevel ErrorCorrectionLevel::L(0, 0x01, "L");
  ErrorCorrectionLevel ErrorCorrectionLevel::M(1, 0x00, "M");
  ErrorCorrectionLevel ErrorCorrectionLevel::Q(2, 0x03, "Q");
  ErrorCorrectionLevel ErrorCorrectionLevel::H(3, 0x02, "H");
ErrorCorrectionLevel *ErrorCorrectionLevel::FOR_BITS[] = { &M, &L, &H, &Q };
int ErrorCorrectionLevel::N_LEVELS = 4;

}
}

// file: zxing/qrcode/FormatInformation.cpp

/*
 *  FormatInformation.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 18/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/FormatInformation.h>
// #include <limits>

namespace zxing {
namespace qrcode {

using namespace std;

int FormatInformation::FORMAT_INFO_MASK_QR = 0x5412;
int FormatInformation::FORMAT_INFO_DECODE_LOOKUP[][2] = { { 0x5412, 0x00 }, { 0x5125, 0x01 }, { 0x5E7C, 0x02 }, {
    0x5B4B, 0x03 }, { 0x45F9, 0x04 }, { 0x40CE, 0x05 }, { 0x4F97, 0x06 }, { 0x4AA0, 0x07 }, { 0x77C4, 0x08 }, {
    0x72F3, 0x09 }, { 0x7DAA, 0x0A }, { 0x789D, 0x0B }, { 0x662F, 0x0C }, { 0x6318, 0x0D }, { 0x6C41, 0x0E }, {
    0x6976, 0x0F }, { 0x1689, 0x10 }, { 0x13BE, 0x11 }, { 0x1CE7, 0x12 }, { 0x19D0, 0x13 }, { 0x0762, 0x14 }, {
    0x0255, 0x15 }, { 0x0D0C, 0x16 }, { 0x083B, 0x17 }, { 0x355F, 0x18 }, { 0x3068, 0x19 }, { 0x3F31, 0x1A }, {
    0x3A06, 0x1B }, { 0x24B4, 0x1C }, { 0x2183, 0x1D }, { 0x2EDA, 0x1E }, { 0x2BED, 0x1F },
};
int FormatInformation::N_FORMAT_INFO_DECODE_LOOKUPS = 32;

int FormatInformation::BITS_SET_IN_HALF_BYTE[] = { 0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4 };

FormatInformation::FormatInformation(int formatInfo) :
    errorCorrectionLevel_(ErrorCorrectionLevel::forBits((formatInfo >> 3) & 0x03)), dataMask_((char)(formatInfo & 0x07)) {
}

ErrorCorrectionLevel& FormatInformation::getErrorCorrectionLevel() {
  return errorCorrectionLevel_;
}

char FormatInformation::getDataMask() {
  return dataMask_;
}

int FormatInformation::numBitsDiffering(int a, int b) {
  a ^= b;
  return BITS_SET_IN_HALF_BYTE[a & 0x0F] + BITS_SET_IN_HALF_BYTE[(a >> 4 & 0x0F)] + BITS_SET_IN_HALF_BYTE[(a >> 8
         & 0x0F)] + BITS_SET_IN_HALF_BYTE[(a >> 12 & 0x0F)] + BITS_SET_IN_HALF_BYTE[(a >> 16 & 0x0F)]
         + BITS_SET_IN_HALF_BYTE[(a >> 20 & 0x0F)] + BITS_SET_IN_HALF_BYTE[(a >> 24 & 0x0F)]
         + BITS_SET_IN_HALF_BYTE[(a >> 28 & 0x0F)];
}

Ref<FormatInformation> FormatInformation::decodeFormatInformation(int maskedFormatInfo1, int maskedFormatInfo2) {
  Ref<FormatInformation> result(doDecodeFormatInformation(maskedFormatInfo1, maskedFormatInfo2));
  if (result != 0) {
    return result;
  }
  // Should return null, but, some QR codes apparently
  // do not mask this info. Try again by actually masking the pattern
  // first
  return doDecodeFormatInformation(maskedFormatInfo1 ^ FORMAT_INFO_MASK_QR,
                                   maskedFormatInfo2  ^ FORMAT_INFO_MASK_QR);
}
Ref<FormatInformation> FormatInformation::doDecodeFormatInformation(int maskedFormatInfo1, int maskedFormatInfo2) {
  // Find the int in FORMAT_INFO_DECODE_LOOKUP with fewest bits differing
  int bestDifference = numeric_limits<int>::max();
  int bestFormatInfo = 0;
  for (int i = 0; i < N_FORMAT_INFO_DECODE_LOOKUPS; i++) {
    int* decodeInfo = FORMAT_INFO_DECODE_LOOKUP[i];
    int targetInfo = decodeInfo[0];
    if (targetInfo == maskedFormatInfo1 || targetInfo == maskedFormatInfo2) {
      // Found an exact match
      Ref<FormatInformation> result(new FormatInformation(decodeInfo[1]));
      return result;
    }
    int bitsDifference = numBitsDiffering(maskedFormatInfo1, targetInfo);
    if (bitsDifference < bestDifference) {
      bestFormatInfo = decodeInfo[1];
      bestDifference = bitsDifference;
    }
    if (maskedFormatInfo1 != maskedFormatInfo2) {
        // also try the other option
        bitsDifference = numBitsDiffering(maskedFormatInfo2, targetInfo);
        if (bitsDifference < bestDifference) {
            bestFormatInfo = decodeInfo[1];
          bestDifference = bitsDifference;
        }
      }
  }
  if (bestDifference <= 3) {
    Ref<FormatInformation> result(new FormatInformation(bestFormatInfo));
    return result;
  }
  Ref<FormatInformation> result;
  return result;
}

bool operator==(const FormatInformation &a, const FormatInformation &b) {
  return &(a.errorCorrectionLevel_) == &(b.errorCorrectionLevel_) && a.dataMask_ == b.dataMask_;
}

ostream& operator<<(ostream& out, const FormatInformation& fi) {
  const FormatInformation *fip = &fi;
  out << "FormatInformation @ " << fip;
  return out;
}

}
}

// file: zxing/qrcode/QRCodeReader.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  QRCodeReader.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 20/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/QRCodeReader.h>
// #include <zxing/qrcode/detector/Detector.h>

// #include <iostream>

namespace zxing {
	namespace qrcode {

		using namespace std;

		QRCodeReader::QRCodeReader() :decoder_() {
		}
		//TODO: see if any of the other files in the qrcode tree need tryHarder
		Ref<Result> QRCodeReader::decode(Ref<BinaryBitmap> image, DecodeHints hints) {
			Detector detector(image->getBlackMatrix());
			Ref<DetectorResult> detectorResult(detector.detect(hints));
			ArrayRef< Ref<ResultPoint> > points (detectorResult->getPoints());
			Ref<DecoderResult> decoderResult(decoder_.decode(detectorResult->getBits()));
			Ref<Result> result(
							   new Result(decoderResult->getText(), decoderResult->getRawBytes(), points, BarcodeFormat::QR_CODE));
			return result;
		}

		QRCodeReader::~QRCodeReader() {
		}

    Decoder& QRCodeReader::getDecoder() {
        return decoder_;
    }
	}
}

// file: zxing/qrcode/Version.cpp

/*
 *  Version.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 14/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/Version.h>
// #include <zxing/qrcode/FormatInformation.h>
// #include <zxing/FormatException.h>
// #include <limits>
// #include <iostream>
// #include <cstdarg>

using std::vector;
using std::numeric_limits;

namespace zxing {
namespace qrcode {

ECB::ECB(int count, int dataCodewords) :
    count_(count), dataCodewords_(dataCodewords) {
}

int ECB::getCount() {
  return count_;
}

int ECB::getDataCodewords() {
  return dataCodewords_;
}

ECBlocks::ECBlocks(int ecCodewords, ECB *ecBlocks) :
    ecCodewords_(ecCodewords), ecBlocks_(1, ecBlocks) {
}

ECBlocks::ECBlocks(int ecCodewords, ECB *ecBlocks1, ECB *ecBlocks2) :
    ecCodewords_(ecCodewords), ecBlocks_(1, ecBlocks1) {
  ecBlocks_.push_back(ecBlocks2);
}

int ECBlocks::getECCodewords() {
  return ecCodewords_;
}

std::vector<ECB*>& ECBlocks::getECBlocks() {
  return ecBlocks_;
}

ECBlocks::~ECBlocks() {
  for (size_t i = 0; i < ecBlocks_.size(); i++) {
    delete ecBlocks_[i];
  }
}

unsigned int Version::VERSION_DECODE_INFO[] = { 0x07C94, 0x085BC, 0x09A99, 0x0A4D3, 0x0BBF6, 0x0C762, 0x0D847, 0x0E60D,
    0x0F928, 0x10B78, 0x1145D, 0x12A17, 0x13532, 0x149A6, 0x15683, 0x168C9, 0x177EC, 0x18EC4, 0x191E1, 0x1AFAB,
    0x1B08E, 0x1CC1A, 0x1D33F, 0x1ED75, 0x1F250, 0x209D5, 0x216F0, 0x228BA, 0x2379F, 0x24B0B, 0x2542E, 0x26A64,
    0x27541, 0x28C69
                                              };
int Version::N_VERSION_DECODE_INFOS = 34;
vector<Ref<Version> > Version::VERSIONS;
static int N_VERSIONS = Version::buildVersions();

int Version::getVersionNumber() {
  return versionNumber_;
}

vector<int> &Version::getAlignmentPatternCenters() {
  return alignmentPatternCenters_;
}

int Version::getTotalCodewords() {
  return totalCodewords_;
}

int Version::getDimensionForVersion() {
  return 17 + 4 * versionNumber_;
}

ECBlocks& Version::getECBlocksForLevel(ErrorCorrectionLevel &ecLevel) {
  return *ecBlocks_[ecLevel.ordinal()];
}

Version *Version::getProvisionalVersionForDimension(int dimension) {
  if (dimension % 4 != 1) {
    throw FormatException();
  }
  try {
    return Version::getVersionForNumber((dimension - 17) >> 2);
  } catch (IllegalArgumentException const& ignored) {
    (void)ignored;
    throw FormatException();
  }
}

Version *Version::getVersionForNumber(int versionNumber) {
  if (versionNumber < 1 || versionNumber > N_VERSIONS) {
    throw ReaderException("versionNumber must be between 1 and 40");
  }

  return VERSIONS[versionNumber - 1];
}

Version::Version(int versionNumber, vector<int> *alignmentPatternCenters, ECBlocks *ecBlocks1, ECBlocks *ecBlocks2,
                 ECBlocks *ecBlocks3, ECBlocks *ecBlocks4) :
    versionNumber_(versionNumber), alignmentPatternCenters_(*alignmentPatternCenters), ecBlocks_(4), totalCodewords_(0) {
  ecBlocks_[0] = ecBlocks1;
  ecBlocks_[1] = ecBlocks2;
  ecBlocks_[2] = ecBlocks3;
  ecBlocks_[3] = ecBlocks4;

  int total = 0;
  int ecCodewords = ecBlocks1->getECCodewords();
  vector<ECB*> &ecbArray = ecBlocks1->getECBlocks();
  for (size_t i = 0; i < ecbArray.size(); i++) {
    ECB *ecBlock = ecbArray[i];
    total += ecBlock->getCount() * (ecBlock->getDataCodewords() + ecCodewords);
  }
  totalCodewords_ = total;
}

Version::~Version() {
  delete &alignmentPatternCenters_;
  for (size_t i = 0; i < ecBlocks_.size(); i++) {
    delete ecBlocks_[i];
  }
}

Version *Version::decodeVersionInformation(unsigned int versionBits) {
  int bestDifference = numeric_limits<int>::max();
  int bestVersion = 0;
  for (int i = 0; i < N_VERSION_DECODE_INFOS; i++) {
    unsigned targetVersion = VERSION_DECODE_INFO[i];
    // Do the version info bits match exactly? done.
    if (targetVersion == versionBits) {
      return getVersionForNumber(i + 7);
    }
    // Otherwise see if this is the closest to a real version info bit
    // string we have seen so far
    int bitsDifference = FormatInformation::numBitsDiffering(versionBits, targetVersion);
    if (bitsDifference < bestDifference) {
      bestVersion = i + 7;
      bestDifference = bitsDifference;
    }
  }
  // We can tolerate up to 3 bits of error since no two version info codewords will
  // differ in less than 4 bits.
  if (bestDifference <= 3) {
    return getVersionForNumber(bestVersion);
  }
  // If we didn't find a close enough match, fail
  return 0;
}

Ref<BitMatrix> Version::buildFunctionPattern() {
  int dimension = getDimensionForVersion();
  Ref<BitMatrix> functionPattern(new BitMatrix(dimension));


  // Top left finder pattern + separator + format
  functionPattern->setRegion(0, 0, 9, 9);
  // Top right finder pattern + separator + format
  functionPattern->setRegion(dimension - 8, 0, 8, 9);
  // Bottom left finder pattern + separator + format
  functionPattern->setRegion(0, dimension - 8, 9, 8);


  // Alignment patterns
  size_t max = alignmentPatternCenters_.size();
  for (size_t x = 0; x < max; x++) {
    int i = alignmentPatternCenters_[x] - 2;
    for (size_t y = 0; y < max; y++) {
      if ((x == 0 && (y == 0 || y == max - 1)) || (x == max - 1 && y == 0)) {
        // No alignment patterns near the three finder patterns
        continue;
      }
      functionPattern->setRegion(alignmentPatternCenters_[y] - 2, i, 5, 5);
    }
  }

  // Vertical timing pattern
  functionPattern->setRegion(6, 9, 1, dimension - 17);
  // Horizontal timing pattern
  functionPattern->setRegion(9, 6, dimension - 17, 1);

  if (versionNumber_ > 6) {
    // Version info, top right
    functionPattern->setRegion(dimension - 11, 0, 3, 6);
    // Version info, bottom left
    functionPattern->setRegion(0, dimension - 11, 6, 3);
  }

  return functionPattern;
}

static vector<int> *intArray(size_t n...) {
  va_list ap;
  va_start(ap, n);
  vector<int> *result = new vector<int>(n);
  for (size_t i = 0; i < n; i++) {
    (*result)[i] = va_arg(ap, int);
  }
  va_end(ap);
  return result;
}

int Version::buildVersions() {
  VERSIONS.push_back(Ref<Version>(new Version(1, intArray(0),
                                  new ECBlocks(7, new ECB(1, 19)),
                                  new ECBlocks(10, new ECB(1, 16)),
                                  new ECBlocks(13, new ECB(1, 13)),
                                  new ECBlocks(17, new ECB(1, 9)))));
  VERSIONS.push_back(Ref<Version>(new Version(2, intArray(2, 6, 18),
                                  new ECBlocks(10, new ECB(1, 34)),
                                  new ECBlocks(16, new ECB(1, 28)),
                                  new ECBlocks(22, new ECB(1, 22)),
                                  new ECBlocks(28, new ECB(1, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(3, intArray(2, 6, 22),
                                  new ECBlocks(15, new ECB(1, 55)),
                                  new ECBlocks(26, new ECB(1, 44)),
                                  new ECBlocks(18, new ECB(2, 17)),
                                  new ECBlocks(22, new ECB(2, 13)))));
  VERSIONS.push_back(Ref<Version>(new Version(4, intArray(2, 6, 26),
                                  new ECBlocks(20, new ECB(1, 80)),
                                  new ECBlocks(18, new ECB(2, 32)),
                                  new ECBlocks(26, new ECB(2, 24)),
                                  new ECBlocks(16, new ECB(4, 9)))));
  VERSIONS.push_back(Ref<Version>(new Version(5, intArray(2, 6, 30),
                                  new ECBlocks(26, new ECB(1, 108)),
                                  new ECBlocks(24, new ECB(2, 43)),
                                  new ECBlocks(18, new ECB(2, 15),
                                               new ECB(2, 16)),
                                  new ECBlocks(22, new ECB(2, 11),
                                               new ECB(2, 12)))));
  VERSIONS.push_back(Ref<Version>(new Version(6, intArray(2, 6, 34),
                                  new ECBlocks(18, new ECB(2, 68)),
                                  new ECBlocks(16, new ECB(4, 27)),
                                  new ECBlocks(24, new ECB(4, 19)),
                                  new ECBlocks(28, new ECB(4, 15)))));
  VERSIONS.push_back(Ref<Version>(new Version(7, intArray(3, 6, 22, 38),
                                  new ECBlocks(20, new ECB(2, 78)),
                                  new ECBlocks(18, new ECB(4, 31)),
                                  new ECBlocks(18, new ECB(2, 14),
                                               new ECB(4, 15)),
                                  new ECBlocks(26, new ECB(4, 13),
                                               new ECB(1, 14)))));
  VERSIONS.push_back(Ref<Version>(new Version(8, intArray(3, 6, 24, 42),
                                  new ECBlocks(24, new ECB(2, 97)),
                                  new ECBlocks(22, new ECB(2, 38),
                                               new ECB(2, 39)),
                                  new ECBlocks(22, new ECB(4, 18),
                                               new ECB(2, 19)),
                                  new ECBlocks(26, new ECB(4, 14),
                                               new ECB(2, 15)))));
  VERSIONS.push_back(Ref<Version>(new Version(9, intArray(3, 6, 26, 46),
                                  new ECBlocks(30, new ECB(2, 116)),
                                  new ECBlocks(22, new ECB(3, 36),
                                               new ECB(2, 37)),
                                  new ECBlocks(20, new ECB(4, 16),
                                               new ECB(4, 17)),
                                  new ECBlocks(24, new ECB(4, 12),
                                               new ECB(4, 13)))));
  VERSIONS.push_back(Ref<Version>(new Version(10, intArray(3, 6, 28, 50),
                                  new ECBlocks(18, new ECB(2, 68),
                                               new ECB(2, 69)),
                                  new ECBlocks(26, new ECB(4, 43),
                                               new ECB(1, 44)),
                                  new ECBlocks(24, new ECB(6, 19),
                                               new ECB(2, 20)),
                                  new ECBlocks(28, new ECB(6, 15),
                                               new ECB(2, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(11, intArray(3, 6, 30, 54),
                                  new ECBlocks(20, new ECB(4, 81)),
                                  new ECBlocks(30, new ECB(1, 50),
                                               new ECB(4, 51)),
                                  new ECBlocks(28, new ECB(4, 22),
                                               new ECB(4, 23)),
                                  new ECBlocks(24, new ECB(3, 12),
                                               new ECB(8, 13)))));
  VERSIONS.push_back(Ref<Version>(new Version(12, intArray(3, 6, 32, 58),
                                  new ECBlocks(24, new ECB(2, 92),
                                               new ECB(2, 93)),
                                  new ECBlocks(22, new ECB(6, 36),
                                               new ECB(2, 37)),
                                  new ECBlocks(26, new ECB(4, 20),
                                               new ECB(6, 21)),
                                  new ECBlocks(28, new ECB(7, 14),
                                               new ECB(4, 15)))));
  VERSIONS.push_back(Ref<Version>(new Version(13, intArray(3, 6, 34, 62),
                                  new ECBlocks(26, new ECB(4, 107)),
                                  new ECBlocks(22, new ECB(8, 37),
                                               new ECB(1, 38)),
                                  new ECBlocks(24, new ECB(8, 20),
                                               new ECB(4, 21)),
                                  new ECBlocks(22, new ECB(12, 11),
                                               new ECB(4, 12)))));
  VERSIONS.push_back(Ref<Version>(new Version(14, intArray(4, 6, 26, 46, 66),
                                  new ECBlocks(30, new ECB(3, 115),
                                               new ECB(1, 116)),
                                  new ECBlocks(24, new ECB(4, 40),
                                               new ECB(5, 41)),
                                  new ECBlocks(20, new ECB(11, 16),
                                               new ECB(5, 17)),
                                  new ECBlocks(24, new ECB(11, 12),
                                               new ECB(5, 13)))));
  VERSIONS.push_back(Ref<Version>(new Version(15, intArray(4, 6, 26, 48, 70),
                                  new ECBlocks(22, new ECB(5, 87),
                                               new ECB(1, 88)),
                                  new ECBlocks(24, new ECB(5, 41),
                                               new ECB(5, 42)),
                                  new ECBlocks(30, new ECB(5, 24),
                                               new ECB(7, 25)),
                                  new ECBlocks(24, new ECB(11, 12),
                                               new ECB(7, 13)))));
  VERSIONS.push_back(Ref<Version>(new Version(16, intArray(4, 6, 26, 50, 74),
                                  new ECBlocks(24, new ECB(5, 98),
                                               new ECB(1, 99)),
                                  new ECBlocks(28, new ECB(7, 45),
                                               new ECB(3, 46)),
                                  new ECBlocks(24, new ECB(15, 19),
                                               new ECB(2, 20)),
                                  new ECBlocks(30, new ECB(3, 15),
                                               new ECB(13, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(17, intArray(4, 6, 30, 54, 78),
                                  new ECBlocks(28, new ECB(1, 107),
                                               new ECB(5, 108)),
                                  new ECBlocks(28, new ECB(10, 46),
                                               new ECB(1, 47)),
                                  new ECBlocks(28, new ECB(1, 22),
                                               new ECB(15, 23)),
                                  new ECBlocks(28, new ECB(2, 14),
                                               new ECB(17, 15)))));
  VERSIONS.push_back(Ref<Version>(new Version(18, intArray(4, 6, 30, 56, 82),
                                  new ECBlocks(30, new ECB(5, 120),
                                               new ECB(1, 121)),
                                  new ECBlocks(26, new ECB(9, 43),
                                               new ECB(4, 44)),
                                  new ECBlocks(28, new ECB(17, 22),
                                               new ECB(1, 23)),
                                  new ECBlocks(28, new ECB(2, 14),
                                               new ECB(19, 15)))));
  VERSIONS.push_back(Ref<Version>(new Version(19, intArray(4, 6, 30, 58, 86),
                                  new ECBlocks(28, new ECB(3, 113),
                                               new ECB(4, 114)),
                                  new ECBlocks(26, new ECB(3, 44),
                                               new ECB(11, 45)),
                                  new ECBlocks(26, new ECB(17, 21),
                                               new ECB(4, 22)),
                                  new ECBlocks(26, new ECB(9, 13),
                                               new ECB(16, 14)))));
  VERSIONS.push_back(Ref<Version>(new Version(20, intArray(4, 6, 34, 62, 90),
                                  new ECBlocks(28, new ECB(3, 107),
                                               new ECB(5, 108)),
                                  new ECBlocks(26, new ECB(3, 41),
                                               new ECB(13, 42)),
                                  new ECBlocks(30, new ECB(15, 24),
                                               new ECB(5, 25)),
                                  new ECBlocks(28, new ECB(15, 15),
                                               new ECB(10, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(21, intArray(5, 6, 28, 50, 72, 94),
                                  new ECBlocks(28, new ECB(4, 116),
                                               new ECB(4, 117)),
                                  new ECBlocks(26, new ECB(17, 42)),
                                  new ECBlocks(28, new ECB(17, 22),
                                               new ECB(6, 23)),
                                  new ECBlocks(30, new ECB(19, 16),
                                               new ECB(6, 17)))));
  VERSIONS.push_back(Ref<Version>(new Version(22, intArray(5, 6, 26, 50, 74, 98),
                                  new ECBlocks(28, new ECB(2, 111),
                                               new ECB(7, 112)),
                                  new ECBlocks(28, new ECB(17, 46)),
                                  new ECBlocks(30, new ECB(7, 24),
                                               new ECB(16, 25)),
                                  new ECBlocks(24, new ECB(34, 13)))));
  VERSIONS.push_back(Ref<Version>(new Version(23, intArray(5, 6, 30, 54, 78, 102),
                                  new ECBlocks(30, new ECB(4, 121),
                                               new ECB(5, 122)),
                                  new ECBlocks(28, new ECB(4, 47),
                                               new ECB(14, 48)),
                                  new ECBlocks(30, new ECB(11, 24),
                                               new ECB(14, 25)),
                                  new ECBlocks(30, new ECB(16, 15),
                                               new ECB(14, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(24, intArray(5, 6, 28, 54, 80, 106),
                                  new ECBlocks(30, new ECB(6, 117),
                                               new ECB(4, 118)),
                                  new ECBlocks(28, new ECB(6, 45),
                                               new ECB(14, 46)),
                                  new ECBlocks(30, new ECB(11, 24),
                                               new ECB(16, 25)),
                                  new ECBlocks(30, new ECB(30, 16),
                                               new ECB(2, 17)))));
  VERSIONS.push_back(Ref<Version>(new Version(25, intArray(5, 6, 32, 58, 84, 110),
                                  new ECBlocks(26, new ECB(8, 106),
                                               new ECB(4, 107)),
                                  new ECBlocks(28, new ECB(8, 47),
                                               new ECB(13, 48)),
                                  new ECBlocks(30, new ECB(7, 24),
                                               new ECB(22, 25)),
                                  new ECBlocks(30, new ECB(22, 15),
                                               new ECB(13, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(26, intArray(5, 6, 30, 58, 86, 114),
                                  new ECBlocks(28, new ECB(10, 114),
                                               new ECB(2, 115)),
                                  new ECBlocks(28, new ECB(19, 46),
                                               new ECB(4, 47)),
                                  new ECBlocks(28, new ECB(28, 22),
                                               new ECB(6, 23)),
                                  new ECBlocks(30, new ECB(33, 16),
                                               new ECB(4, 17)))));
  VERSIONS.push_back(Ref<Version>(new Version(27, intArray(5, 6, 34, 62, 90, 118),
                                  new ECBlocks(30, new ECB(8, 122),
                                               new ECB(4, 123)),
                                  new ECBlocks(28, new ECB(22, 45),
                                               new ECB(3, 46)),
                                  new ECBlocks(30, new ECB(8, 23),
                                               new ECB(26, 24)),
                                  new ECBlocks(30, new ECB(12, 15),
                                               new ECB(28, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(28, intArray(6, 6, 26, 50, 74, 98, 122),
                                  new ECBlocks(30, new ECB(3, 117),
                                               new ECB(10, 118)),
                                  new ECBlocks(28, new ECB(3, 45),
                                               new ECB(23, 46)),
                                  new ECBlocks(30, new ECB(4, 24),
                                               new ECB(31, 25)),
                                  new ECBlocks(30, new ECB(11, 15),
                                               new ECB(31, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(29, intArray(6, 6, 30, 54, 78, 102, 126),
                                  new ECBlocks(30, new ECB(7, 116),
                                               new ECB(7, 117)),
                                  new ECBlocks(28, new ECB(21, 45),
                                               new ECB(7, 46)),
                                  new ECBlocks(30, new ECB(1, 23),
                                               new ECB(37, 24)),
                                  new ECBlocks(30, new ECB(19, 15),
                                               new ECB(26, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(30, intArray(6, 6, 26, 52, 78, 104, 130),
                                  new ECBlocks(30, new ECB(5, 115),
                                               new ECB(10, 116)),
                                  new ECBlocks(28, new ECB(19, 47),
                                               new ECB(10, 48)),
                                  new ECBlocks(30, new ECB(15, 24),
                                               new ECB(25, 25)),
                                  new ECBlocks(30, new ECB(23, 15),
                                               new ECB(25, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(31, intArray(6, 6, 30, 56, 82, 108, 134),
                                  new ECBlocks(30, new ECB(13, 115),
                                               new ECB(3, 116)),
                                  new ECBlocks(28, new ECB(2, 46),
                                               new ECB(29, 47)),
                                  new ECBlocks(30, new ECB(42, 24),
                                               new ECB(1, 25)),
                                  new ECBlocks(30, new ECB(23, 15),
                                               new ECB(28, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(32, intArray(6, 6, 34, 60, 86, 112, 138),
                                  new ECBlocks(30, new ECB(17, 115)),
                                  new ECBlocks(28, new ECB(10, 46),
                                               new ECB(23, 47)),
                                  new ECBlocks(30, new ECB(10, 24),
                                               new ECB(35, 25)),
                                  new ECBlocks(30, new ECB(19, 15),
                                               new ECB(35, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(33, intArray(6, 6, 30, 58, 86, 114, 142),
                                  new ECBlocks(30, new ECB(17, 115),
                                               new ECB(1, 116)),
                                  new ECBlocks(28, new ECB(14, 46),
                                               new ECB(21, 47)),
                                  new ECBlocks(30, new ECB(29, 24),
                                               new ECB(19, 25)),
                                  new ECBlocks(30, new ECB(11, 15),
                                               new ECB(46, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(34, intArray(6, 6, 34, 62, 90, 118, 146),
                                  new ECBlocks(30, new ECB(13, 115),
                                               new ECB(6, 116)),
                                  new ECBlocks(28, new ECB(14, 46),
                                               new ECB(23, 47)),
                                  new ECBlocks(30, new ECB(44, 24),
                                               new ECB(7, 25)),
                                  new ECBlocks(30, new ECB(59, 16),
                                               new ECB(1, 17)))));
  VERSIONS.push_back(Ref<Version>(new Version(35, intArray(7, 6, 30, 54, 78,
                                  102, 126, 150),
                                  new ECBlocks(30, new ECB(12, 121),
                                               new ECB(7, 122)),
                                  new ECBlocks(28, new ECB(12, 47),
                                               new ECB(26, 48)),
                                  new ECBlocks(30, new ECB(39, 24),
                                               new ECB(14, 25)),
                                  new ECBlocks(30, new ECB(22, 15),
                                               new ECB(41, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(36, intArray(7, 6, 24, 50, 76,
                                  102, 128, 154),
                                  new ECBlocks(30, new ECB(6, 121),
                                               new ECB(14, 122)),
                                  new ECBlocks(28, new ECB(6, 47),
                                               new ECB(34, 48)),
                                  new ECBlocks(30, new ECB(46, 24),
                                               new ECB(10, 25)),
                                  new ECBlocks(30, new ECB(2, 15),
                                               new ECB(64, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(37, intArray(7, 6, 28, 54, 80,
                                  106, 132, 158),
                                  new ECBlocks(30, new ECB(17, 122),
                                               new ECB(4, 123)),
                                  new ECBlocks(28, new ECB(29, 46),
                                               new ECB(14, 47)),
                                  new ECBlocks(30, new ECB(49, 24),
                                               new ECB(10, 25)),
                                  new ECBlocks(30, new ECB(24, 15),
                                               new ECB(46, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(38, intArray(7, 6, 32, 58, 84,
                                  110, 136, 162),
                                  new ECBlocks(30, new ECB(4, 122),
                                               new ECB(18, 123)),
                                  new ECBlocks(28, new ECB(13, 46),
                                               new ECB(32, 47)),
                                  new ECBlocks(30, new ECB(48, 24),
                                               new ECB(14, 25)),
                                  new ECBlocks(30, new ECB(42, 15),
                                               new ECB(32, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(39, intArray(7, 6, 26, 54, 82,
                                  110, 138, 166),
                                  new ECBlocks(30, new ECB(20, 117),
                                               new ECB(4, 118)),
                                  new ECBlocks(28, new ECB(40, 47),
                                               new ECB(7, 48)),
                                  new ECBlocks(30, new ECB(43, 24),
                                               new ECB(22, 25)),
                                  new ECBlocks(30, new ECB(10, 15),
                                               new ECB(67, 16)))));
  VERSIONS.push_back(Ref<Version>(new Version(40, intArray(7, 6, 30, 58, 86,
                                  114, 142, 170),
                                  new ECBlocks(30, new ECB(19, 118),
                                               new ECB(6, 119)),
                                  new ECBlocks(28, new ECB(18, 47),
                                               new ECB(31, 48)),
                                  new ECBlocks(30, new ECB(34, 24),
                                               new ECB(34, 25)),
                                  new ECBlocks(30, new ECB(20, 15),
                                               new ECB(61, 16)))));
  return (int)VERSIONS.size();
}

}
}

// file: zxing/qrcode/decoder/BitMatrixParser.cpp

/*
 *  BitMatrixParser.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 20/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/decoder/BitMatrixParser.h>
// #include <zxing/qrcode/decoder/DataMask.h>


namespace zxing {
namespace qrcode {

int BitMatrixParser::copyBit(size_t x, size_t y, int versionBits) {
  return bitMatrix_->get(x, y) ? (versionBits << 1) | 0x1 : versionBits << 1;
}

BitMatrixParser::BitMatrixParser(Ref<BitMatrix> bitMatrix) :
    bitMatrix_(bitMatrix), parsedVersion_(0), parsedFormatInfo_() {
  size_t dimension = bitMatrix->getHeight();
  if ((dimension < 21) || (dimension & 0x03) != 1) {
    throw ReaderException("Dimension must be 1 mod 4 and >= 21");
  }
}

Ref<FormatInformation> BitMatrixParser::readFormatInformation() {
  if (parsedFormatInfo_ != 0) {
    return parsedFormatInfo_;
  }

  // Read top-left format info bits
  int formatInfoBits1 = 0;
  for (int i = 0; i < 6; i++) {
    formatInfoBits1 = copyBit(i, 8, formatInfoBits1);
  }
  // .. and skip a bit in the timing pattern ...
  formatInfoBits1 = copyBit(7, 8, formatInfoBits1);
  formatInfoBits1 = copyBit(8, 8, formatInfoBits1);
  formatInfoBits1 = copyBit(8, 7, formatInfoBits1);
  // .. and skip a bit in the timing pattern ...
  for (int j = 5; j >= 0; j--) {
    formatInfoBits1 = copyBit(8, j, formatInfoBits1);
  }

  // Read the top-right/bottom-left pattern
  int dimension = bitMatrix_->getHeight();
  int formatInfoBits2 = 0;
  int jMin = dimension - 7;
  for (int j = dimension - 1; j >= jMin; j--) {
    formatInfoBits2 = copyBit(8, j, formatInfoBits2);
  }
  for (int i = dimension - 8; i < dimension; i++) {
    formatInfoBits2 = copyBit(i, 8, formatInfoBits2);
  }

  parsedFormatInfo_ = FormatInformation::decodeFormatInformation(formatInfoBits1,formatInfoBits2);
  if (parsedFormatInfo_ != 0) {
    return parsedFormatInfo_;
  }
  throw ReaderException("Could not decode format information");
}

Version *BitMatrixParser::readVersion() {
  if (parsedVersion_ != 0) {
    return parsedVersion_;
  }

  int dimension = bitMatrix_->getHeight();

  int provisionalVersion = (dimension - 17) >> 2;
  if (provisionalVersion <= 6) {
    return Version::getVersionForNumber(provisionalVersion);
  }

  // Read top-right version info: 3 wide by 6 tall
  int versionBits = 0;
  for (int y = 5; y >= 0; y--) {
    int xMin = dimension - 11;
    for (int x = dimension - 9; x >= xMin; x--) {
      versionBits = copyBit(x, y, versionBits);
    }
  }

  parsedVersion_ = Version::decodeVersionInformation(versionBits);
  if (parsedVersion_ != 0 && parsedVersion_->getDimensionForVersion() == dimension) {
    return parsedVersion_;
  }

  // Hmm, failed. Try bottom left: 6 wide by 3 tall
  versionBits = 0;
  for (int x = 5; x >= 0; x--) {
    int yMin = dimension - 11;
    for (int y = dimension - 9; y >= yMin; y--) {
      versionBits = copyBit(x, y, versionBits);
    }
  }

  parsedVersion_ = Version::decodeVersionInformation(versionBits);
  if (parsedVersion_ != 0 && parsedVersion_->getDimensionForVersion() == dimension) {
    return parsedVersion_;
  }
  throw ReaderException("Could not decode version");
}

ArrayRef<char> BitMatrixParser::readCodewords() {
  Ref<FormatInformation> formatInfo = readFormatInformation();
  Version *version = readVersion();


  // Get the data mask for the format used in this QR Code. This will exclude
  // some bits from reading as we wind through the bit matrix.
  DataMask &dataMask = DataMask::forReference((int)formatInfo->getDataMask());
  //	cout << (int)formatInfo->getDataMask() << endl;
  int dimension = bitMatrix_->getHeight();
  dataMask.unmaskBitMatrix(*bitMatrix_, dimension);


  //		cerr << *bitMatrix_ << endl;
  //	cerr << version->getTotalCodewords() << endl;

  Ref<BitMatrix> functionPattern = version->buildFunctionPattern();


  //	cout << *functionPattern << endl;

  bool readingUp = true;
  ArrayRef<char> result(version->getTotalCodewords());
  int resultOffset = 0;
  int currentByte = 0;
  int bitsRead = 0;
  // Read columns in pairs, from right to left
  for (int x = dimension - 1; x > 0; x -= 2) {
    if (x == 6) {
      // Skip whole column with vertical alignment pattern;
      // saves time and makes the other code proceed more cleanly
      x--;
    }
    // Read alternatingly from bottom to top then top to bottom
    for (int counter = 0; counter < dimension; counter++) {
      int y = readingUp ? dimension - 1 - counter : counter;
      for (int col = 0; col < 2; col++) {
        // Ignore bits covered by the function pattern
        if (!functionPattern->get(x - col, y)) {
          // Read a bit
          bitsRead++;
          currentByte <<= 1;
          if (bitMatrix_->get(x - col, y)) {
            currentByte |= 1;
          }
          // If we've made a whole byte, save it off
          if (bitsRead == 8) {
            result[resultOffset++] = (char)currentByte;
            bitsRead = 0;
            currentByte = 0;
          }
        }
      }
    }
    readingUp = !readingUp; // switch directions
  }

  if (resultOffset != version->getTotalCodewords()) {
    throw ReaderException("Did not read all codewords");
  }
  return result;
}

}
}

// file: zxing/qrcode/decoder/DataBlock.cpp

/*
 *  DataBlock.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 19/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/decoder/DataBlock.h>
// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
namespace qrcode {

using namespace std;

DataBlock::DataBlock(int numDataCodewords, ArrayRef<char> codewords) :
    numDataCodewords_(numDataCodewords), codewords_(codewords) {
}

int DataBlock::getNumDataCodewords() {
  return numDataCodewords_;
}

ArrayRef<char> DataBlock::getCodewords() {
  return codewords_;
}


std::vector<Ref<DataBlock> > DataBlock::getDataBlocks(ArrayRef<char> rawCodewords, Version *version,
    ErrorCorrectionLevel &ecLevel) {


  // Figure out the number and size of data blocks used by this version and
  // error correction level
  ECBlocks &ecBlocks = version->getECBlocksForLevel(ecLevel);


  // First count the total number of data blocks
  int totalBlocks = 0;
  vector<ECB*> ecBlockArray = ecBlocks.getECBlocks();
  for (size_t i = 0; i < ecBlockArray.size(); i++) {
    totalBlocks += ecBlockArray[i]->getCount();
  }

  // Now establish DataBlocks of the appropriate size and number of data codewords
  std::vector<Ref<DataBlock> > result(totalBlocks);
  int numResultBlocks = 0;
  for (size_t j = 0; j < ecBlockArray.size(); j++) {
    ECB *ecBlock = ecBlockArray[j];
    for (int i = 0; i < ecBlock->getCount(); i++) {
      int numDataCodewords = ecBlock->getDataCodewords();
      int numBlockCodewords = ecBlocks.getECCodewords() + numDataCodewords;
      ArrayRef<char> buffer(numBlockCodewords);
      Ref<DataBlock> blockRef(new DataBlock(numDataCodewords, buffer));
      result[numResultBlocks++] = blockRef;
    }
  }

  // All blocks have the same amount of data, except that the last n
  // (where n may be 0) have 1 more byte. Figure out where these start.
  int shorterBlocksTotalCodewords = (int)result[0]->codewords_->size();
  int longerBlocksStartAt = (int)result.size() - 1;
  while (longerBlocksStartAt >= 0) {
    int numCodewords = (int)result[longerBlocksStartAt]->codewords_->size();
    if (numCodewords == shorterBlocksTotalCodewords) {
      break;
    }
    if (numCodewords != shorterBlocksTotalCodewords + 1) {
      throw IllegalArgumentException("Data block sizes differ by more than 1");
    }
    longerBlocksStartAt--;
  }
  longerBlocksStartAt++;

  int shorterBlocksNumDataCodewords = shorterBlocksTotalCodewords - ecBlocks.getECCodewords();
  // The last elements of result may be 1 element longer;
  // first fill out as many elements as all of them have
  int rawCodewordsOffset = 0;
  for (int i = 0; i < shorterBlocksNumDataCodewords; i++) {
    for (int j = 0; j < numResultBlocks; j++) {
      result[j]->codewords_[i] = rawCodewords[rawCodewordsOffset++];
    }
  }
  // Fill out the last data block in the longer ones
  for (int j = longerBlocksStartAt; j < numResultBlocks; j++) {
    result[j]->codewords_[shorterBlocksNumDataCodewords] = rawCodewords[rawCodewordsOffset++];
  }
  // Now add in error correction blocks
  int max = (int)result[0]->codewords_->size();
  for (int i = shorterBlocksNumDataCodewords; i < max; i++) {
    for (int j = 0; j < numResultBlocks; j++) {
      int iOffset = j < longerBlocksStartAt ? i : i + 1;
      result[j]->codewords_[iOffset] = rawCodewords[rawCodewordsOffset++];
    }
  }

  if (rawCodewordsOffset != rawCodewords->size()) {
    throw IllegalArgumentException("rawCodewordsOffset != rawCodewords.length");
  }

  return result;
}

}
}

// file: zxing/qrcode/decoder/DataMask.cpp

/*
 *  DataMask.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 19/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/decoder/DataMask.h>

// #include <zxing/common/IllegalArgumentException.h>

namespace zxing {
namespace qrcode {

using namespace std;

DataMask::DataMask() {
}

DataMask::~DataMask() {
}

vector<Ref<DataMask> > DataMask::DATA_MASKS;
static int N_DATA_MASKS = DataMask::buildDataMasks();

DataMask &DataMask::forReference(int reference) {
  if (reference < 0 || reference > 7) {
    throw IllegalArgumentException("reference must be between 0 and 7");
  }
  return *DATA_MASKS[reference];
}

void DataMask::unmaskBitMatrix(BitMatrix& bits, size_t dimension) {
  for (size_t y = 0; y < dimension; y++) {
    for (size_t x = 0; x < dimension; x++) {
      // TODO: check why the coordinates have to be swapped
      if (isMasked(y, x)) {
        bits.flip(x, y);
      }
    }
  }
}

/**
 * 000: mask bits for which (x + y) mod 2 == 0
 */
class DataMask000 : public DataMask {
public:
  bool isMasked(size_t x, size_t y) {
    //		return ((x + y) & 0x01) == 0;
    return ((x + y) % 2) == 0;
  }
};

/**
 * 001: mask bits for which x mod 2 == 0
 */
class DataMask001 : public DataMask {
public:
  bool isMasked(size_t x, size_t) {
    //		return (x & 0x01) == 0;
    return (x % 2) == 0;
  }
};

/**
 * 010: mask bits for which y mod 3 == 0
 */
class DataMask010 : public DataMask {
public:
  bool isMasked(size_t, size_t y) {
    return y % 3 == 0;
  }
};

/**
 * 011: mask bits for which (x + y) mod 3 == 0
 */
class DataMask011 : public DataMask {
public:
  bool isMasked(size_t x, size_t y) {
    return (x + y) % 3 == 0;
  }
};

/**
 * 100: mask bits for which (x/2 + y/3) mod 2 == 0
 */
class DataMask100 : public DataMask {
public:
  bool isMasked(size_t x, size_t y) {
    //		return (((x >> 1) + (y / 3)) & 0x01) == 0;
    return (((x >> 1) + (y / 3)) % 2) == 0;
  }
};

/**
 * 101: mask bits for which xy mod 2 + xy mod 3 == 0
 */
class DataMask101 : public DataMask {
public:
  bool isMasked(size_t x, size_t y) {
    size_t temp = x * y;
    //		return (temp & 0x01) + (temp % 3) == 0;
    return (temp % 2) + (temp % 3) == 0;

  }
};

/**
 * 110: mask bits for which (xy mod 2 + xy mod 3) mod 2 == 0
 */
class DataMask110 : public DataMask {
public:
  bool isMasked(size_t x, size_t y) {
    size_t temp = x * y;
    //		return (((temp & 0x01) + (temp % 3)) & 0x01) == 0;
    return (((temp % 2) + (temp % 3)) % 2) == 0;
  }
};

/**
 * 111: mask bits for which ((x+y)mod 2 + xy mod 3) mod 2 == 0
 */
class DataMask111 : public DataMask {
public:
  bool isMasked(size_t x, size_t y) {
    //		return ((((x + y) & 0x01) + ((x * y) % 3)) & 0x01) == 0;
    return ((((x + y) % 2) + ((x * y) % 3)) % 2) == 0;
  }
};

int DataMask::buildDataMasks() {
  DATA_MASKS.push_back(Ref<DataMask> (new DataMask000()));
  DATA_MASKS.push_back(Ref<DataMask> (new DataMask001()));
  DATA_MASKS.push_back(Ref<DataMask> (new DataMask010()));
  DATA_MASKS.push_back(Ref<DataMask> (new DataMask011()));
  DATA_MASKS.push_back(Ref<DataMask> (new DataMask100()));
  DATA_MASKS.push_back(Ref<DataMask> (new DataMask101()));
  DATA_MASKS.push_back(Ref<DataMask> (new DataMask110()));
  DATA_MASKS.push_back(Ref<DataMask> (new DataMask111()));
  return (int)DATA_MASKS.size();
}

}
}

// file: zxing/qrcode/decoder/DecodedBitStreamParser.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  DecodedBitStreamParser.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 20/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/decoder/DecodedBitStreamParser.h>
// #include <zxing/common/CharacterSetECI.h>
// #include <zxing/FormatException.h>
// #include <zxing/common/StringUtils.h>
// #include <iostream>
#ifndef NO_ICONV
// #include <iconv.h>
#endif

// Required for compatibility. TODO: test on Symbian
#ifdef ZXING_ICONV_CONST
#undef ICONV_CONST
#define ICONV_CONST const
#endif

#ifndef ICONV_CONST
#define ICONV_CONST /**/
#endif

namespace zxing {
namespace qrcode {
using namespace std;
using namespace zxing::common;

const char DecodedBitStreamParser::ALPHANUMERIC_CHARS[] =
  { '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B',
    'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N',
    'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X',
    'Y', 'Z', ' ', '$', '%', '*', '+', '-', '.', '/', ':'
  };

namespace {int GB2312_SUBSET = 1;}

#ifdef kPrefixBinary
/*
 base64.cpp and base64.h ([here: just the encoding part!]
 
 Copyright (C) 2004-2008 Ren� Nyffenegger
 
 This source code is provided 'as-is', without any express or implied
 warranty. In no event will the author be held liable for any damages
 arising from the use of this software.
 
 Permission is granted to anyone to use this software for any purpose,
 including commercial applications, and to alter it and redistribute it
 freely, subject to the following restrictions:
 
 1. The origin of this source code must not be misrepresented; you must not
 claim that you wrote the original source code. If you use this source code
 in a product, an acknowledgment in the product documentation would be
 appreciated but is not required.
 
 2. Altered source versions must be plainly marked as such, and must not be
 misrepresented as being the original source code.
 
 3. This notice may not be removed or altered from any source distribution.
 
 Ren� Nyffenegger rene.nyffenegger@adp-gmbh.ch
 http://www.adp-gmbh.ch/cpp/common/base64.html
 */
static const std::string base64_chars =
"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
"abcdefghijklmnopqrstuvwxyz"
"0123456789+/";

std::string base64_encode(char const* bytes_to_encode, size_t in_len) {
    std::string ret;
    int i = 0
    ,   j = 0;
    unsigned char char_array_3[3]
    ,             char_array_4[4];
    
    while (in_len--) {
        char_array_3[i++] = *(bytes_to_encode++);
        if (i == 3) {
            char_array_4[0] = (char_array_3[0] & 0xfc) >> 2;
            char_array_4[1] = ((char_array_3[0] & 0x03) << 4) + ((char_array_3[1] & 0xf0) >> 4);
            char_array_4[2] = ((char_array_3[1] & 0x0f) << 2) + ((char_array_3[2] & 0xc0) >> 6);
            char_array_4[3] = char_array_3[2] & 0x3f;
            
            for(i = 0; (i <4) ; i++)
                ret += base64_chars[char_array_4[i]];
            i = 0;
        }
    }
    
    if (i)
    {
        for(j = i; j < 3; j++)
            char_array_3[j] = '\0';
        
        char_array_4[0] = (char_array_3[0] & 0xfc) >> 2;
        char_array_4[1] = ((char_array_3[0] & 0x03) << 4) + ((char_array_3[1] & 0xf0) >> 4);
        char_array_4[2] = ((char_array_3[1] & 0x0f) << 2) + ((char_array_3[2] & 0xc0) >> 6);
        char_array_4[3] = char_array_3[2] & 0x3f;
        
        for (j = 0; (j < i + 1); j++)
            ret += base64_chars[char_array_4[j]];
        
        while((i++ < 3))
            ret += '=';
    }
    
    return ret;
}
// end base64
#endif

void DecodedBitStreamParser::append(std::string &result,
                                    string const& in,
                                    const char *src) {
  append(result, (char const*)in.c_str(), in.length(), src);
}

void DecodedBitStreamParser::append(std::string &result,
                                    const char *bufIn,
                                    size_t nIn,
                                    const char *src) {
#ifdef kPrefixBinary
    if (result.find(kPrefixBinary) == 0) { // prefix has to be found - at the beginning
        // here the QR-code is multipart (prefix ends with plain alphanumerics), so result already contains that prefix)
        if (result.length() > kPrefixLength) { // can be longer than total prefix-length (some more alphanumeric character(s) following)
            // these extra chars must be moved from the end of intermediate result to beginning of bufIn, so they're included in base64
            size_t nTmp = result.length() - kPrefixLength;
            string tmpStr = result.substr(kPrefixLength, nTmp);
            char* tmpbuf = new char[nTmp + nIn];
            memcpy(tmpbuf, (unsigned char const*)tmpStr.c_str(), nTmp);
            memcpy(tmpbuf + nTmp, bufIn, nIn);
            result = result.substr(0, kPrefixLength);
            result.append(base64_encode(tmpbuf, nTmp + nIn));
            delete[] tmpbuf;
        } else {
            result.append(base64_encode(bufIn, nIn));
        }
        return;
    } else if (nIn >= kPrefixLength) { // but maybe the QR-code is *not* multipart, all contents comes at once
        size_t i
        , l = sizeof(kPrefixBinary) - 1; // without 0-terminator
        for (i = 0; i < nIn && i < l && bufIn[i] == kPrefixBinary[i]; i++);
        if (i == l) {
            result.append((const char *)bufIn, kPrefixLength);
            result.append(base64_encode(bufIn + kPrefixLength, nIn - kPrefixLength));
            return;
        }
    }
#endif
    
#ifndef NO_ICONV
  if (nIn == 0) {
    return;
  }

  iconv_t cd = iconv_open(StringUtils::UTF8, src);
  if (cd == (iconv_t)-1) {
    result.append((const char *)bufIn, nIn);
 } else {
     const int maxOut = (int)(4 * nIn + 1);
     char* bufOut = new char[maxOut];
     
     ICONV_CONST char *fromPtr = (ICONV_CONST char *)bufIn;
     size_t nFrom = nIn;
     char *toPtr = (char *)bufOut;
     size_t nTo = maxOut;
     
     while (nFrom > 0) {
         size_t oneway = iconv(cd, &fromPtr, &nFrom, &toPtr, &nTo);
         if (oneway == (size_t)(-1)) {
             iconv_close(cd);
             delete[] bufOut;
             throw ReaderException("error converting characters");
         }
     }
     iconv_close(cd);
     
     int nResult = (int)(maxOut - nTo);
     bufOut[nResult] = '\0';
     result.append((const char *)bufOut);
     delete[] bufOut;
 }
#else
  result.append((const char *)bufIn, nIn);
#endif
}

void DecodedBitStreamParser::decodeHanziSegment(Ref<BitSource> bits_,
                                                string& result,
                                                int count) {
  BitSource& bits (*bits_);
  // Don't crash trying to read more bits than we have available.
  if (count * 13 > bits.available()) {
    throw FormatException();
  }

  // Each character will require 2 bytes. Read the characters as 2-byte pairs
  // and decode as GB2312 afterwards
  size_t nBytes = 2 * count;
  char* buffer = new char[nBytes];
  int offset = 0;
  while (count > 0) {
    // Each 13 bits encodes a 2-byte character
    int twoBytes = bits.readBits(13);
    int assembledTwoBytes = ((twoBytes / 0x060) << 8) | (twoBytes % 0x060);
    if (assembledTwoBytes < 0x003BF) {
      // In the 0xA1A1 to 0xAAFE range
      assembledTwoBytes += 0x0A1A1;
    } else {
      // In the 0xB0A1 to 0xFAFE range
      assembledTwoBytes += 0x0A6A1;
    }
    buffer[offset] = (char) ((assembledTwoBytes >> 8) & 0xFF);
    buffer[offset + 1] = (char) (assembledTwoBytes & 0xFF);
    offset += 2;
    count--;
  }

  try {
    append(result, buffer, nBytes, StringUtils::GB2312);
  } catch (ReaderException const& ignored) {
    (void)ignored;
    delete [] buffer;
    throw FormatException();
  }

  delete [] buffer;
}

void DecodedBitStreamParser::decodeKanjiSegment(Ref<BitSource> bits, std::string &result, int count) {
  // Each character will require 2 bytes. Read the characters as 2-byte pairs
  // and decode as Shift_JIS afterwards
  size_t nBytes = 2 * count;
  char* buffer = new char[nBytes];
  int offset = 0;
  while (count > 0) {
    // Each 13 bits encodes a 2-byte character

    int twoBytes = bits->readBits(13);
    int assembledTwoBytes = ((twoBytes / 0x0C0) << 8) | (twoBytes % 0x0C0);
    if (assembledTwoBytes < 0x01F00) {
      // In the 0x8140 to 0x9FFC range
      assembledTwoBytes += 0x08140;
    } else {
      // In the 0xE040 to 0xEBBF range
      assembledTwoBytes += 0x0C140;
    }
    buffer[offset] = (char)(assembledTwoBytes >> 8);
    buffer[offset + 1] = (char)assembledTwoBytes;
    offset += 2;
    count--;
  }
  try {
    append(result, buffer, nBytes, StringUtils::SHIFT_JIS);
  } catch (ReaderException const& ignored) {
    (void)ignored;
    delete [] buffer;
    throw FormatException();
  }
  delete[] buffer;
}

void DecodedBitStreamParser::decodeByteSegment(Ref<BitSource> bits_,
                                               string& result,
                                               int count,
                                               CharacterSetECI* currentCharacterSetECI,
                                               ArrayRef< ArrayRef<char> >& byteSegments,
                                               Hashtable const& hints) {
  int nBytes = count;
  BitSource& bits (*bits_);
  // Don't crash trying to read more bits than we have available.
  if (count << 3 > bits.available()) {
    throw FormatException();
  }

  ArrayRef<char> bytes_ (count);
  char* readBytes = &(*bytes_)[0];
  for (int i = 0; i < count; i++) {
    readBytes[i] = (char) bits.readBits(8);
  }
  string encoding;
  if (currentCharacterSetECI == 0) {
    // The spec isn't clear on this mode; see
    // section 6.4.5: t does not say which encoding to assuming
    // upon decoding. I have seen ISO-8859-1 used as well as
    // Shift_JIS -- without anything like an ECI designator to
    // give a hint.
    encoding = StringUtils::guessEncoding(readBytes, count, hints);
  } else {
    encoding = currentCharacterSetECI->name();
  }
  try {
    append(result, readBytes, nBytes, encoding.c_str());
  } catch (ReaderException const& ignored) {
    (void)ignored;
    throw FormatException();
  }
  byteSegments->values().push_back(bytes_);
}

void DecodedBitStreamParser::decodeNumericSegment(Ref<BitSource> bits, std::string &result, int count) {
  int nBytes = count;
  char* bytes = new char[nBytes];
  int i = 0;
  // Read three digits at a time
  while (count >= 3) {
    // Each 10 bits encodes three digits
    if (bits->available() < 10) {
      delete[] bytes;
      throw ReaderException("format exception");
    }
    int threeDigitsBits = bits->readBits(10);
    if (threeDigitsBits >= 1000) {
      ostringstream s;
      s << "Illegal value for 3-digit unit: " << threeDigitsBits;
      delete[] bytes;
      throw ReaderException(s.str().c_str());
    }
    bytes[i++] = ALPHANUMERIC_CHARS[threeDigitsBits / 100];
    bytes[i++] = ALPHANUMERIC_CHARS[(threeDigitsBits / 10) % 10];
    bytes[i++] = ALPHANUMERIC_CHARS[threeDigitsBits % 10];
    count -= 3;
  }
  if (count == 2) {
    if (bits->available() < 7) {
      delete[] bytes;
      throw ReaderException("format exception");
    }
    // Two digits left over to read, encoded in 7 bits
    int twoDigitsBits = bits->readBits(7);
    if (twoDigitsBits >= 100) {
      ostringstream s;
      s << "Illegal value for 2-digit unit: " << twoDigitsBits;
      delete[] bytes;
      throw ReaderException(s.str().c_str());
    }
    bytes[i++] = ALPHANUMERIC_CHARS[twoDigitsBits / 10];
    bytes[i++] = ALPHANUMERIC_CHARS[twoDigitsBits % 10];
  } else if (count == 1) {
    if (bits->available() < 4) {
      delete[] bytes;
      throw ReaderException("format exception");
    }
    // One digit left over to read
    int digitBits = bits->readBits(4);
    if (digitBits >= 10) {
      ostringstream s;
      s << "Illegal value for digit unit: " << digitBits;
      delete[] bytes;
      throw ReaderException(s.str().c_str());
    }
    bytes[i++] = ALPHANUMERIC_CHARS[digitBits];
  }
  append(result, bytes, nBytes, StringUtils::ASCII);
  delete[] bytes;
}

char DecodedBitStreamParser::toAlphaNumericChar(size_t value) {
  if (value >= sizeof(DecodedBitStreamParser::ALPHANUMERIC_CHARS)) {
    throw FormatException();
  }
  return ALPHANUMERIC_CHARS[value];
}

void DecodedBitStreamParser::decodeAlphanumericSegment(Ref<BitSource> bits_,
                                                       string& result,
                                                       int count,
                                                       bool fc1InEffect) {
  BitSource& bits (*bits_);
  ostringstream bytes;
  // Read two characters at a time
  while (count > 1) {
    if (bits.available() < 11) {
      throw FormatException();
    }
    int nextTwoCharsBits = bits.readBits(11);
    bytes << toAlphaNumericChar(nextTwoCharsBits / 45);
    bytes << toAlphaNumericChar(nextTwoCharsBits % 45);
    count -= 2;
  }
  if (count == 1) {
    // special case: one character left
    if (bits.available() < 6) {
      throw FormatException();
    }
    bytes << toAlphaNumericChar(bits.readBits(6));
  }
  // See section 6.4.8.1, 6.4.8.2
  string s = bytes.str();
  if (fc1InEffect) {
    // We need to massage the result a bit if in an FNC1 mode:
    ostringstream r;
    for (size_t i = 0; i < s.length(); i++) {
      if (s[i] != '%') {
        r << s[i];
      } else {
        if (i < s.length() - 1 && s[i + 1] == '%') {
          // %% is rendered as %
          r << s[i++];
        } else {
          // In alpha mode, % should be converted to FNC1 separator 0x1D
          r << (char)0x1D;
        }
      }
    }
    s = r.str();
  }
  append(result, s, StringUtils::ASCII);
}

namespace {
  int parseECIValue(BitSource& bits) {
    int firstByte = bits.readBits(8);
    if ((firstByte & 0x80) == 0) {
      // just one byte
      return firstByte & 0x7F;
    }
    if ((firstByte & 0xC0) == 0x80) {
      // two bytes
      int secondByte = bits.readBits(8);
      return ((firstByte & 0x3F) << 8) | secondByte;
    }
    if ((firstByte & 0xE0) == 0xC0) {
      // three bytes
      int secondThirdBytes = bits.readBits(16);
      return ((firstByte & 0x1F) << 16) | secondThirdBytes;
    }
    throw FormatException();
  }
}

Ref<DecoderResult>
DecodedBitStreamParser::decode(ArrayRef<char> bytes,
                               Version* version,
                               ErrorCorrectionLevel const& ecLevel,
                               Hashtable const& hints) {
  Ref<BitSource> bits_ (new BitSource(bytes));
  BitSource& bits (*bits_);
  string result;
  result.reserve(50);
  ArrayRef< ArrayRef<char> > byteSegments (0);
  try {
    CharacterSetECI* currentCharacterSetECI = 0;
    bool fc1InEffect = false;
    Mode* mode = 0;
    do {
      // While still another segment to read...
      if (bits.available() < 4) {
        // OK, assume we're done. Really, a TERMINATOR mode should have been recorded here
        mode = &Mode::TERMINATOR;
      } else {
        try {
          mode = &Mode::forBits(bits.readBits(4)); // mode is encoded by 4 bits
        } catch (IllegalArgumentException const& iae) {
          throw iae;
          // throw FormatException.getFormatInstance();
        }
      }
      if (mode != &Mode::TERMINATOR) {
        if ((mode == &Mode::FNC1_FIRST_POSITION) || (mode == &Mode::FNC1_SECOND_POSITION)) {
          // We do little with FNC1 except alter the parsed result a bit according to the spec
          fc1InEffect = true;
        } else if (mode == &Mode::STRUCTURED_APPEND) {
          if (bits.available() < 16) {
            throw FormatException();
          }
          // not really supported; all we do is ignore it
          // Read next 8 bits (symbol sequence #) and 8 bits (parity data), then continue
          bits.readBits(16);
        } else if (mode == &Mode::ECI) {
          // Count doesn't apply to ECI
          int value = parseECIValue(bits);
          currentCharacterSetECI = CharacterSetECI::getCharacterSetECIByValue(value);
          if (currentCharacterSetECI == 0) {
            throw FormatException();
          }
        } else {
          // First handle Hanzi mode which does not start with character count
          if (mode == &Mode::HANZI) {
            //chinese mode contains a sub set indicator right after mode indicator
            int subset = bits.readBits(4);
            int countHanzi = bits.readBits(mode->getCharacterCountBits(version));
            if (subset == GB2312_SUBSET) {
              decodeHanziSegment(bits_, result, countHanzi);
            }
          } else {
            // "Normal" QR code modes:
            // How many characters will follow, encoded in this mode?
            int count = bits.readBits(mode->getCharacterCountBits(version));
            if (mode == &Mode::NUMERIC) {
              decodeNumericSegment(bits_, result, count);
            } else if (mode == &Mode::ALPHANUMERIC) {
              decodeAlphanumericSegment(bits_, result, count, fc1InEffect);
            } else if (mode == &Mode::BYTE) {
              decodeByteSegment(bits_, result, count, currentCharacterSetECI, byteSegments, hints);
            } else if (mode == &Mode::KANJI) {
              decodeKanjiSegment(bits_, result, count);
            } else {
              throw FormatException();
            }
          }
        }
      }
    } while (mode != &Mode::TERMINATOR);
  } catch (IllegalArgumentException const& iae) {
    (void)iae;
    // from readBits() calls
    throw FormatException();
  }

  return Ref<DecoderResult>(new DecoderResult(bytes, Ref<String>(new String(result)), byteSegments, (string)ecLevel));
}
}
}

// file: zxing/qrcode/decoder/Decoder.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Decoder.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 20/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/decoder/Decoder.h>
// #include <zxing/qrcode/decoder/BitMatrixParser.h>
// #include <zxing/qrcode/ErrorCorrectionLevel.h>
// #include <zxing/qrcode/Version.h>
// #include <zxing/qrcode/decoder/DataBlock.h>
// #include <zxing/qrcode/decoder/DecodedBitStreamParser.h>
// #include <zxing/ReaderException.h>
// #include <zxing/ChecksumException.h>
// #include <zxing/common/reedsolomon/ReedSolomonException.h>

namespace zxing {
namespace qrcode {
        
Decoder::Decoder() :
  rsDecoder_(GenericGF::QR_CODE_FIELD_256) {
}

void Decoder::correctErrors(ArrayRef<char> codewordBytes, int numDataCodewords) {
  int numCodewords = (int)codewordBytes->size();
  ArrayRef<int> codewordInts(numCodewords);
  for (int i = 0; i < numCodewords; i++) {
    codewordInts[i] = codewordBytes[i] & 0xff;
  }
  int numECCodewords = numCodewords - numDataCodewords;

  try {
    rsDecoder_.decode(codewordInts, numECCodewords);
  } catch (ReedSolomonException const& ignored) {
    (void)ignored;
    throw ChecksumException();
  }

  for (int i = 0; i < numDataCodewords; i++) {
    codewordBytes[i] = (char)codewordInts[i];
  }
}

Ref<DecoderResult> Decoder::decode(Ref<BitMatrix> bits) {
  // Construct a parser and read version, error-correction level
  BitMatrixParser parser(bits);

  // std::cerr << *bits << std::endl;

  Version *version = parser.readVersion();
  ErrorCorrectionLevel &ecLevel = parser.readFormatInformation()->getErrorCorrectionLevel();

  // Read codewords
  ArrayRef<char> codewords(parser.readCodewords());


  // Separate into data blocks
  std::vector<Ref<DataBlock> > dataBlocks(DataBlock::getDataBlocks(codewords, version, ecLevel));


  // Count total number of data bytes
  int totalBytes = 0;
  for (size_t i = 0; i < dataBlocks.size(); i++) {
    totalBytes += dataBlocks[i]->getNumDataCodewords();
  }
  ArrayRef<char> resultBytes(totalBytes);
  int resultOffset = 0;


  // Error-correct and copy data blocks together into a stream of bytes
  for (size_t j = 0; j < dataBlocks.size(); j++) {
    Ref<DataBlock> dataBlock(dataBlocks[j]);
    ArrayRef<char> codewordBytes = dataBlock->getCodewords();
    int numDataCodewords = dataBlock->getNumDataCodewords();
    correctErrors(codewordBytes, numDataCodewords);
    for (int i = 0; i < numDataCodewords; i++) {
      resultBytes[resultOffset++] = codewordBytes[i];
    }
  }

  return DecodedBitStreamParser::decode(resultBytes,
                                        version,
                                        ecLevel,
                                        DecodedBitStreamParser::Hashtable());
}
}
}

// file: zxing/qrcode/decoder/Mode.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Mode.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 19/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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
// #include <zxing/qrcode/decoder/Mode.h>
// #include <zxing/common/Counted.h>
// #include <zxing/ReaderException.h>
// #include <zxing/qrcode/Version.h>
// #include <sstream>

namespace zxing {
namespace qrcode {
    
Mode Mode::TERMINATOR(0, 0, 0, 0x00, "TERMINATOR");
Mode Mode::NUMERIC(10, 12, 14, 0x01, "NUMERIC");
Mode Mode::ALPHANUMERIC(9, 11, 13, 0x02, "ALPHANUMERIC");
Mode Mode::STRUCTURED_APPEND(0, 0, 0, 0x03, "STRUCTURED_APPEND");
Mode Mode::BYTE(8, 16, 16, 0x04, "BYTE");
Mode Mode::ECI(0, 0, 0, 0x07, "ECI");
Mode Mode::KANJI(8, 10, 12, 0x08, "KANJI");
Mode Mode::FNC1_FIRST_POSITION(0, 0, 0, 0x05, "FNC1_FIRST_POSITION");
Mode Mode::FNC1_SECOND_POSITION(0, 0, 0, 0x09, "FNC1_SECOND_POSITION");
Mode Mode::HANZI(8, 10, 12, 0x0D, "HANZI");

Mode::Mode(int cbv0_9, int cbv10_26, int cbv27, int /* bits */, char const* name) :
  characterCountBitsForVersions0To9_(cbv0_9), characterCountBitsForVersions10To26_(cbv10_26),
  characterCountBitsForVersions27AndHigher_(cbv27), name_(name) {
}

Mode& Mode::forBits(int bits) {
  switch (bits) {
  case 0x0:
    return TERMINATOR;
  case 0x1:
    return NUMERIC;
  case 0x2:
    return ALPHANUMERIC;
  case 0x3:
    return STRUCTURED_APPEND;
  case 0x4:
    return BYTE;
  case 0x5:
    return FNC1_FIRST_POSITION;
  case 0x7:
    return ECI;
  case 0x8:
    return KANJI;
  case 0x9:
    return FNC1_SECOND_POSITION;
  case 0xD:
    // 0xD is defined in GBT 18284-2000, may not be supported in foreign country
    return HANZI;
  default:
    ostringstream s;
    s << "Illegal mode bits: " << bits;
    throw ReaderException(s.str().c_str());
  }
}

int Mode::getCharacterCountBits(Version *version) {
  int number = version->getVersionNumber();
  if (number <= 9) {
    return characterCountBitsForVersions0To9_;
  } else if (number <= 26) {
    return characterCountBitsForVersions10To26_;
  } else {
    return characterCountBitsForVersions27AndHigher_;
  }
}
}
}

// file: zxing/qrcode/detector/AlignmentPattern.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  AlignmentPattern.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/detector/AlignmentPattern.h>

namespace zxing {
namespace qrcode {
        
AlignmentPattern::AlignmentPattern(float posX, float posY, float estimatedModuleSize) :
    ResultPoint(posX,posY), estimatedModuleSize_(estimatedModuleSize) {
}

bool AlignmentPattern::aboutEquals(float moduleSize, float i, float j) const {
  if (abs(i - getY()) <= moduleSize && abs(j - getX()) <= moduleSize) {
    float moduleSizeDiff = abs(moduleSize - estimatedModuleSize_);
    return moduleSizeDiff <= 1.0f || moduleSizeDiff <= estimatedModuleSize_;
  }
  return false;
}

Ref<AlignmentPattern> AlignmentPattern::combineEstimate(float i, float j, float newModuleSize) const {
  float combinedX = (getX() + j) / 2.0f;
  float combinedY = (getY() + i) / 2.0f;
  float combinedModuleSize = (estimatedModuleSize_ + newModuleSize) / 2.0f;
  Ref<AlignmentPattern> result
      (new AlignmentPattern(combinedX, combinedY, combinedModuleSize));
  return result;
}
}
}

// file: zxing/qrcode/detector/AlignmentPatternFinder.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/detector/AlignmentPatternFinder.h>
// #include <zxing/ReaderException.h>
// #include <zxing/common/BitArray.h>
// #include <vector>
// #include <cmath>
// #include <cstdlib>

namespace zxing {
namespace qrcode {

float AlignmentPatternFinder::centerFromEnd(vector<int>& stateCount, int end) {
  return (float)(end - stateCount[2]) - stateCount[1] / 2.0f;
}

bool AlignmentPatternFinder::foundPatternCross(vector<int> &stateCount) {
  float maxVariance = moduleSize_ / 2.0f;
  for (int i = 0; i < 3; i++) {
    if (abs(moduleSize_ - stateCount[i]) >= maxVariance) {
      return false;
    }
  }
  return true;
}

float AlignmentPatternFinder::crossCheckVertical(int startI, int centerJ, int maxCount,
                                                 int originalStateCountTotal) {
  int maxI = image_->getHeight();
  vector<int> stateCount(3, 0);


  // Start counting up from center
  int i = startI;
  while (i >= 0 && image_->get(centerJ, i) && stateCount[1] <= maxCount) {
    stateCount[1]++;
    i--;
  }
  // If already too many modules in this state or ran off the edge:
  if (i < 0 || stateCount[1] > maxCount) {
    return nan();
  }
  while (i >= 0 && !image_->get(centerJ, i) && stateCount[0] <= maxCount) {
    stateCount[0]++;
    i--;
  }
  if (stateCount[0] > maxCount) {
    return nan();
  }

  // Now also count down from center
  i = startI + 1;
  while (i < maxI && image_->get(centerJ, i) && stateCount[1] <= maxCount) {
    stateCount[1]++;
    i++;
  }
  if (i == maxI || stateCount[1] > maxCount) {
    return nan();
  }
  while (i < maxI && !image_->get(centerJ, i) && stateCount[2] <= maxCount) {
    stateCount[2]++;
    i++;
  }
  if (stateCount[2] > maxCount) {
    return nan();
  }

  int stateCountTotal = stateCount[0] + stateCount[1] + stateCount[2];
  if (5 * abs(stateCountTotal - originalStateCountTotal) >= 2 * originalStateCountTotal) {
    return nan();
  }

  return foundPatternCross(stateCount) ? centerFromEnd(stateCount, i) : nan();
}

Ref<AlignmentPattern> AlignmentPatternFinder::handlePossibleCenter(vector<int> &stateCount, int i, int j) {
  int stateCountTotal = stateCount[0] + stateCount[1] + stateCount[2];
  float centerJ = centerFromEnd(stateCount, j);
  float centerI = crossCheckVertical(i, (int)centerJ, 2 * stateCount[1], stateCountTotal);
  if (!isnan(centerI)) {
    float estimatedModuleSize = (float)(stateCount[0] + stateCount[1] + stateCount[2]) / 3.0f;
    int max = (int)possibleCenters_->size();
    for (int index = 0; index < max; index++) {
      Ref<AlignmentPattern> center((*possibleCenters_)[index]);
      // Look for about the same center and module size:
      if (center->aboutEquals(estimatedModuleSize, centerI, centerJ)) {
        return center->combineEstimate(centerI, centerJ, estimatedModuleSize);
      }
    }
    AlignmentPattern *tmp = new AlignmentPattern(centerJ, centerI, estimatedModuleSize);
    // Hadn't found this before; save it
    tmp->retain();
    possibleCenters_->push_back(tmp);
    if (callback_ != 0) {
      callback_->foundPossibleResultPoint(*tmp);
    }
  }
  Ref<AlignmentPattern> result;
  return result;
}

AlignmentPatternFinder::AlignmentPatternFinder(Ref<BitMatrix> image, int startX, int startY, int width,
                                               int height, float moduleSize,
                                               Ref<ResultPointCallback>const& callback) :
    image_(image), possibleCenters_(new vector<AlignmentPattern *> ()), startX_(startX), startY_(startY),
    width_(width), height_(height), moduleSize_(moduleSize), callback_(callback) {
}

AlignmentPatternFinder::~AlignmentPatternFinder() {
  for (int i = 0; i < int(possibleCenters_->size()); i++) {
    (*possibleCenters_)[i]->release();
    (*possibleCenters_)[i] = 0;
  }
  delete possibleCenters_;
}

Ref<AlignmentPattern> AlignmentPatternFinder::find() {
  int maxJ = startX_ + width_;
  int middleI = startY_ + (height_ >> 1);
  //      Ref<BitArray> luminanceRow(new BitArray(width_));
  // We are looking for black/white/black modules in 1:1:1 ratio;
  // this tracks the number of black/white/black modules seen so far
  vector<int> stateCount(3, 0);
  for (int iGen = 0; iGen < height_; iGen++) {
    // Search from middle outwards
    int i = middleI + ((iGen & 0x01) == 0 ? ((iGen + 1) >> 1) : -((iGen + 1) >> 1));
    //        image_->getBlackRow(i, luminanceRow, startX_, width_);
    stateCount[0] = 0;
    stateCount[1] = 0;
    stateCount[2] = 0;
    int j = startX_;
    // Burn off leading white pixels before anything else; if we start in the middle of
    // a white run, it doesn't make sense to count its length, since we don't know if the
    // white run continued to the left of the start point
    while (j < maxJ && !image_->get(j, i)) {
      j++;
    }
    int currentState = 0;
    while (j < maxJ) {
      if (image_->get(j, i)) {
        // Black pixel
        if (currentState == 1) { // Counting black pixels
          stateCount[currentState]++;
        } else { // Counting white pixels
          if (currentState == 2) { // A winner?
            if (foundPatternCross(stateCount)) { // Yes
              Ref<AlignmentPattern> confirmed(handlePossibleCenter(stateCount, i, j));
              if (confirmed != 0) {
                return confirmed;
              }
            }
            stateCount[0] = stateCount[2];
            stateCount[1] = 1;
            stateCount[2] = 0;
            currentState = 1;
          } else {
            stateCount[++currentState]++;
          }
        }
      } else { // White pixel
        if (currentState == 1) { // Counting black pixels
          currentState++;
        }
        stateCount[currentState]++;
      }
      j++;
    }
    if (foundPatternCross(stateCount)) {
      Ref<AlignmentPattern> confirmed(handlePossibleCenter(stateCount, i, maxJ));
      if (confirmed != 0) {
        return confirmed;
      }
    }

  }

  // Hmm, nothing we saw was observed and confirmed twice. If we had
  // any guess at all, return it.
  if (possibleCenters_->size() > 0) {
    Ref<AlignmentPattern> center((*possibleCenters_)[0]);
    return center;
  }

  throw zxing::ReaderException("Could not find alignment pattern");
}
}
}

// file: zxing/qrcode/detector/Detector.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  Detector.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 14/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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
// #include <zxing/qrcode/detector/FinderPatternFinder.h>
// #include <zxing/qrcode/detector/FinderPattern.h>
// #include <zxing/qrcode/detector/AlignmentPattern.h>
// #include <zxing/qrcode/detector/AlignmentPatternFinder.h>
// #include <zxing/qrcode/Version.h>
// #include <zxing/common/GridSampler.h>
// #include <zxing/DecodeHints.h>
// #include <zxing/common/detector/MathUtils.h>
// #include <sstream>
// #include <cstdlib>
// #include <algorithm>  // vs12, std::min und std:max

namespace zxing {
namespace qrcode {
        
Detector::Detector(Ref<BitMatrix> image) :
  image_(image) {
}

Ref<BitMatrix> Detector::getImage() const {
  return image_;
}

Ref<ResultPointCallback> Detector::getResultPointCallback() const {
  return callback_;
}

Ref<DetectorResult> Detector::detect(DecodeHints const& hints) {
  callback_ = hints.getResultPointCallback();
  FinderPatternFinder finder(image_, hints.getResultPointCallback());
  Ref<FinderPatternInfo> info(finder.find(hints));
  return processFinderPatternInfo(info);
}

Ref<DetectorResult> Detector::processFinderPatternInfo(Ref<FinderPatternInfo> info){
  Ref<FinderPattern> topLeft(info->getTopLeft());
  Ref<FinderPattern> topRight(info->getTopRight());
  Ref<FinderPattern> bottomLeft(info->getBottomLeft());

  float moduleSize = calculateModuleSize(topLeft, topRight, bottomLeft);
  if (moduleSize < 1.0f) {
    throw zxing::ReaderException("bad module size");
  }
  int dimension = computeDimension(topLeft, topRight, bottomLeft, moduleSize);
  Version *provisionalVersion = Version::getProvisionalVersionForDimension(dimension);
  int modulesBetweenFPCenters = provisionalVersion->getDimensionForVersion() - 7;

  Ref<AlignmentPattern> alignmentPattern;
  // Anything above version 1 has an alignment pattern
  if (provisionalVersion->getAlignmentPatternCenters().size() > 0) {


    // Guess where a "bottom right" finder pattern would have been
    float bottomRightX = topRight->getX() - topLeft->getX() + bottomLeft->getX();
    float bottomRightY = topRight->getY() - topLeft->getY() + bottomLeft->getY();


    // Estimate that alignment pattern is closer by 3 modules
    // from "bottom right" to known top left location
    float correctionToTopLeft = 1.0f - 3.0f / (float)modulesBetweenFPCenters;
    int estAlignmentX = (int)(topLeft->getX() + correctionToTopLeft * (bottomRightX - topLeft->getX()));
    int estAlignmentY = (int)(topLeft->getY() + correctionToTopLeft * (bottomRightY - topLeft->getY()));


    // Kind of arbitrary -- expand search radius before giving up
    for (int i = 4; i <= 16; i <<= 1) {
      try {
        alignmentPattern = findAlignmentInRegion(moduleSize, estAlignmentX, estAlignmentY, (float)i);
        break;
      } catch (zxing::ReaderException const& re) {
        (void)re;
        // try next round
      }
    }
    if (alignmentPattern == 0) {
      // Try anyway
    }

  }

  Ref<PerspectiveTransform> transform = createTransform(topLeft, topRight, bottomLeft, alignmentPattern, dimension);
  Ref<BitMatrix> bits(sampleGrid(image_, dimension, transform));
  ArrayRef< Ref<ResultPoint> > points(new Array< Ref<ResultPoint> >(alignmentPattern == 0 ? 3 : 4));
  points[0].reset(bottomLeft);
  points[1].reset(topLeft);
  points[2].reset(topRight);
  if (alignmentPattern != 0) {
    points[3].reset(alignmentPattern);
  }

  Ref<DetectorResult> result(new DetectorResult(bits, points));
  return result;
}

Ref<PerspectiveTransform> Detector::createTransform(Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight, Ref <
                                                    ResultPoint > bottomLeft, Ref<ResultPoint> alignmentPattern, int dimension) {

  float dimMinusThree = (float)dimension - 3.5f;
  float bottomRightX;
  float bottomRightY;
  float sourceBottomRightX;
  float sourceBottomRightY;
  if (alignmentPattern != 0) {
    bottomRightX = alignmentPattern->getX();
    bottomRightY = alignmentPattern->getY();
    sourceBottomRightX = dimMinusThree - 3.0f;
    sourceBottomRightY = sourceBottomRightX;
  } else {
    // Don't have an alignment pattern, just make up the bottom-right point
    bottomRightX = (topRight->getX() - topLeft->getX()) + bottomLeft->getX();
    bottomRightY = (topRight->getY() - topLeft->getY()) + bottomLeft->getY();
    sourceBottomRightX = dimMinusThree;
    sourceBottomRightY = dimMinusThree;
  }

  Ref<PerspectiveTransform> transform(PerspectiveTransform::quadrilateralToQuadrilateral(3.5f, 3.5f, dimMinusThree, 3.5f, sourceBottomRightX,
                                                                                         sourceBottomRightY, 3.5f, dimMinusThree, topLeft->getX(), topLeft->getY(), topRight->getX(),
                                                                                         topRight->getY(), bottomRightX, bottomRightY, bottomLeft->getX(), bottomLeft->getY()));

  return transform;
}

Ref<BitMatrix> Detector::sampleGrid(Ref<BitMatrix> image, int dimension, Ref<PerspectiveTransform> transform) {
  GridSampler &sampler = GridSampler::getInstance();
  return sampler.sampleGrid(image, dimension, transform);
}

int Detector::computeDimension(Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight, Ref<ResultPoint> bottomLeft,
                               float moduleSize) {
  int tltrCentersDimension =
    MathUtils::round(ResultPoint::distance(topLeft, topRight) / moduleSize);
  int tlblCentersDimension =
    MathUtils::round(ResultPoint::distance(topLeft, bottomLeft) / moduleSize);
  int dimension = ((tltrCentersDimension + tlblCentersDimension) >> 1) + 7;
  switch (dimension & 0x03) { // mod 4
  case 0:
    dimension++;
    break;
    // 1? do nothing
  case 2:
    dimension--;
    break;
  case 3:
    ostringstream s;
    s << "Bad dimension: " << dimension;
    throw zxing::ReaderException(s.str().c_str());
  }
  return dimension;
}

float Detector::calculateModuleSize(Ref<ResultPoint> topLeft, Ref<ResultPoint> topRight, Ref<ResultPoint> bottomLeft) {
  // Take the average
  return (calculateModuleSizeOneWay(topLeft, topRight) + calculateModuleSizeOneWay(topLeft, bottomLeft)) / 2.0f;
}

float Detector::calculateModuleSizeOneWay(Ref<ResultPoint> pattern, Ref<ResultPoint> otherPattern) {
  float moduleSizeEst1 = sizeOfBlackWhiteBlackRunBothWays((int)pattern->getX(), (int)pattern->getY(),
                                                          (int)otherPattern->getX(), (int)otherPattern->getY());
  float moduleSizeEst2 = sizeOfBlackWhiteBlackRunBothWays((int)otherPattern->getX(), (int)otherPattern->getY(),
                                                          (int)pattern->getX(), (int)pattern->getY());
  if (zxing::isnan(moduleSizeEst1)) {
    return moduleSizeEst2;
  }
  if (zxing::isnan(moduleSizeEst2)) {
    return moduleSizeEst1;
  }
  // Average them, and divide by 7 since we've counted the width of 3 black modules,
  // and 1 white and 1 black module on either side. Ergo, divide sum by 14.
  return (moduleSizeEst1 + moduleSizeEst2) / 14.0f;
}

float Detector::sizeOfBlackWhiteBlackRunBothWays(int fromX, int fromY, int toX, int toY) {

  float result = sizeOfBlackWhiteBlackRun(fromX, fromY, toX, toY);

  // Now count other way -- don't run off image though of course
  float scale = 1.0f;
  int otherToX = fromX - (toX - fromX);
  if (otherToX < 0) {
    scale = (float) fromX / (float) (fromX - otherToX);
    otherToX = 0;
  } else if (otherToX >= (int)image_->getWidth()) {
    scale = (float) (image_->getWidth() - 1 - fromX) / (float) (otherToX - fromX);
    otherToX = image_->getWidth() - 1;
  }
  int otherToY = (int) (fromY - (toY - fromY) * scale);

  scale = 1.0f;
  if (otherToY < 0) {
    scale = (float) fromY / (float) (fromY - otherToY);
    otherToY = 0;
  } else if (otherToY >= (int)image_->getHeight()) {
    scale = (float) (image_->getHeight() - 1 - fromY) / (float) (otherToY - fromY);
    otherToY = image_->getHeight() - 1;
  }
  otherToX = (int) (fromX + (otherToX - fromX) * scale);

  result += sizeOfBlackWhiteBlackRun(fromX, fromY, otherToX, otherToY);

  // Middle pixel is double-counted this way; subtract 1
  return result - 1.0f;
}

float Detector::sizeOfBlackWhiteBlackRun(int fromX, int fromY, int toX, int toY) {
  // Mild variant of Bresenham's algorithm;
  // see http://en.wikipedia.org/wiki/Bresenham's_line_algorithm
  bool steep = abs(toY - fromY) > abs(toX - fromX);
  if (steep) {
    int temp = fromX;
    fromX = fromY;
    fromY = temp;
    temp = toX;
    toX = toY;
    toY = temp;
  }

  int dx = abs(toX - fromX);
  int dy = abs(toY - fromY);
  int error = -dx >> 1;
  int xstep = fromX < toX ? 1 : -1;
  int ystep = fromY < toY ? 1 : -1;

  // In black pixels, looking for white, first or second time.
  int state = 0;
  // Loop up until x == toX, but not beyond
  int xLimit = toX + xstep;
  for (int x = fromX, y = fromY; x != xLimit; x += xstep) {
    int realX = steep ? y : x;
    int realY = steep ? x : y;

    // Does current pixel mean we have moved white to black or vice versa?
    if (!((state == 1) ^ image_->get(realX, realY))) {
      if (state == 2) {
        return MathUtils::distance(x, y, fromX, fromY);
      }
      state++;
    }

    error += dy;
    if (error > 0) {
      if (y == toY) {
        break;
      }
      y += ystep;
      error -= dx;
    }
  }
  // Found black-white-black; give the benefit of the doubt that the next pixel outside the image
  // is "white" so this last point at (toX+xStep,toY) is the right ending. This is really a
  // small approximation; (toX+xStep,toY+yStep) might be really correct. Ignore this.
  if (state == 2) {
    return MathUtils::distance(toX + xstep, toY, fromX, fromY);
  }
  // else we didn't find even black-white-black; no estimate is really possible
  return nan();
}

Ref<AlignmentPattern> Detector::findAlignmentInRegion(float overallEstModuleSize, int estAlignmentX, int estAlignmentY,
                                                      float allowanceFactor) {
  // Look for an alignment pattern (3 modules in size) around where it
  // should be
  int allowance = (int)(allowanceFactor * overallEstModuleSize);
  int alignmentAreaLeftX = max(0, estAlignmentX - allowance);
  int alignmentAreaRightX = min((int)(image_->getWidth() - 1), estAlignmentX + allowance);
  if (alignmentAreaRightX - alignmentAreaLeftX < overallEstModuleSize * 3) {
    throw zxing::ReaderException("region too small to hold alignment pattern");
  }
  int alignmentAreaTopY = max(0, estAlignmentY - allowance);
  int alignmentAreaBottomY = min((int)(image_->getHeight() - 1), estAlignmentY + allowance);
  if (alignmentAreaBottomY - alignmentAreaTopY < overallEstModuleSize * 3) {
    throw zxing::ReaderException("region too small to hold alignment pattern");
  }

  AlignmentPatternFinder alignmentFinder(image_, alignmentAreaLeftX, alignmentAreaTopY, alignmentAreaRightX
                                         - alignmentAreaLeftX, alignmentAreaBottomY - alignmentAreaTopY, overallEstModuleSize, callback_);
  return alignmentFinder.find();
}
}
}

// file: zxing/qrcode/detector/FinderPattern.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  FinderPattern.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

namespace zxing {
namespace qrcode {
        
FinderPattern::FinderPattern(float posX, float posY, float estimatedModuleSize)
    : ResultPoint(posX,posY), estimatedModuleSize_(estimatedModuleSize), count_(1) {}

FinderPattern::FinderPattern(float posX, float posY, float estimatedModuleSize, int count)
    : ResultPoint(posX,posY), estimatedModuleSize_(estimatedModuleSize), count_(count) {}

int FinderPattern::getCount() const {
  return count_;
}

float FinderPattern::getEstimatedModuleSize() const {
  return estimatedModuleSize_;
}

void FinderPattern::incrementCount() {
  count_++;
  // cerr << "ic " << getX() << " " << getY() << " " << count_ << endl;
}

/*
  bool FinderPattern::aboutEquals(float moduleSize, float i, float j) const {
  return abs(i - posY_) <= moduleSize && abs(j - posX_) <= moduleSize && (abs(moduleSize - estimatedModuleSize_)
  <= 1.0f || abs(moduleSize - estimatedModuleSize_) / estimatedModuleSize_ <= 0.1f);
  }
*/
bool FinderPattern::aboutEquals(float moduleSize, float i, float j) const {
  if (abs(i - getY()) <= moduleSize && abs(j - getX()) <= moduleSize) {
    float moduleSizeDiff = abs(moduleSize - estimatedModuleSize_);
    return moduleSizeDiff <= 1.0f || moduleSizeDiff <= estimatedModuleSize_;
  }
  return false;
}

Ref<FinderPattern> FinderPattern::combineEstimate(float i, float j, float newModuleSize) const {
  // fprintf(stderr, "ce %f %f %f\n", i, j, newModuleSize);

  int combinedCount = count_ + 1;
  float combinedX = (count_ * getX() + j) / combinedCount;
  float combinedY = (count_ * getY() + i) / combinedCount;
  float combinedModuleSize = (count_ * getEstimatedModuleSize() + newModuleSize) / combinedCount;
  return Ref<FinderPattern>(new FinderPattern(combinedX, combinedY, combinedModuleSize, combinedCount));
}
}
}

// file: zxing/qrcode/detector/FinderPatternFinder.cpp

// -*- mode:c++; tab-width:2; indent-tabs-mode:nil; c-basic-offset:2 -*-
/*
 *  FinderPatternFinder.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <algorithm>
// #include <zxing/qrcode/detector/FinderPatternFinder.h>
// #include <zxing/ReaderException.h>
// #include <zxing/DecodeHints.h>

namespace zxing {
namespace qrcode {
        
namespace {

class FurthestFromAverageComparator {
private:
  const float averageModuleSize_;
public:
  FurthestFromAverageComparator(float averageModuleSize) :
    averageModuleSize_(averageModuleSize) {
  }
  bool operator()(Ref<FinderPattern> a, Ref<FinderPattern> b) {
    float dA = abs(a->getEstimatedModuleSize() - averageModuleSize_);
    float dB = abs(b->getEstimatedModuleSize() - averageModuleSize_);
    return dA > dB;
  }
};

class CenterComparator {
  const float averageModuleSize_;
public:
  CenterComparator(float averageModuleSize) :
    averageModuleSize_(averageModuleSize) {
  }
  bool operator()(Ref<FinderPattern> a, Ref<FinderPattern> b) {
    // N.B.: we want the result in descending order ...
    if (a->getCount() != b->getCount()) {
      return a->getCount() > b->getCount();
    } else {
      float dA = abs(a->getEstimatedModuleSize() - averageModuleSize_);
      float dB = abs(b->getEstimatedModuleSize() - averageModuleSize_);
      return dA < dB;
    }
  }
};

}

int FinderPatternFinder::CENTER_QUORUM = 2;
int FinderPatternFinder::MIN_SKIP = 3;
int FinderPatternFinder::MAX_MODULES = 57;

float FinderPatternFinder::centerFromEnd(int* stateCount, int end) {
  return (float)(end - stateCount[4] - stateCount[3]) - stateCount[2] / 2.0f;
}

bool FinderPatternFinder::foundPatternCross(int* stateCount) {
  int totalModuleSize = 0;
  for (int i = 0; i < 5; i++) {
    if (stateCount[i] == 0) {
      return false;
    }
    totalModuleSize += stateCount[i];
  }
  if (totalModuleSize < 7) {
    return false;
  }
  float moduleSize = (float)totalModuleSize / 7.0f;
  float maxVariance = moduleSize / 2.0f;
  // Allow less than 50% variance from 1-1-3-1-1 proportions
  return abs(moduleSize - stateCount[0]) < maxVariance && abs(moduleSize - stateCount[1]) < maxVariance && abs(3.0f
         * moduleSize - stateCount[2]) < 3.0f * maxVariance && abs(moduleSize - stateCount[3]) < maxVariance && abs(
           moduleSize - stateCount[4]) < maxVariance;
}

float FinderPatternFinder::crossCheckVertical(size_t startI, size_t centerJ, int maxCount, int originalStateCountTotal) {

  int maxI = image_->getHeight();
  int stateCount[5];
  for (int i = 0; i < 5; i++)
    stateCount[i] = 0;


  // Start counting up from center
  int i = (int)startI;
  while (i >= 0 && image_->get(centerJ, i)) {
    stateCount[2]++;
    i--;
  }
  if (i < 0) {
    return nan();
  }
  while (i >= 0 && !image_->get(centerJ, i) && stateCount[1] <= maxCount) {
    stateCount[1]++;
    i--;
  }
  // If already too many modules in this state or ran off the edge:
  if (i < 0 || stateCount[1] > maxCount) {
    return nan();
  }
  while (i >= 0 && image_->get(centerJ, i) && stateCount[0] <= maxCount) {
    stateCount[0]++;
    i--;
  }
  if (stateCount[0] > maxCount) {
    return nan();
  }

  // Now also count down from center
  i = (int)(startI + 1);
  while (i < maxI && image_->get(centerJ, i)) {
    stateCount[2]++;
    i++;
  }
  if (i == maxI) {
    return nan();
  }
  while (i < maxI && !image_->get(centerJ, i) && stateCount[3] < maxCount) {
    stateCount[3]++;
    i++;
  }
  if (i == maxI || stateCount[3] >= maxCount) {
    return nan();
  }
  while (i < maxI && image_->get(centerJ, i) && stateCount[4] < maxCount) {
    stateCount[4]++;
    i++;
  }
  if (stateCount[4] >= maxCount) {
    return nan();
  }

  // If we found a finder-pattern-like section, but its size is more than 40% different than
  // the original, assume it's a false positive
  int stateCountTotal = stateCount[0] + stateCount[1] + stateCount[2] + stateCount[3] + stateCount[4];
  if (5 * abs(stateCountTotal - originalStateCountTotal) >= 2 * originalStateCountTotal) {
    return nan();
  }

  return foundPatternCross(stateCount) ? centerFromEnd(stateCount, i) : nan();
}

float FinderPatternFinder::crossCheckHorizontal(size_t startJ, size_t centerI, int maxCount,
    int originalStateCountTotal) {

  int maxJ = image_->getWidth();
  int stateCount[5];
  for (int i = 0; i < 5; i++)
    stateCount[i] = 0;

  int j = (int)startJ;
  while (j >= 0 && image_->get(j, centerI)) {
    stateCount[2]++;
    j--;
  }
  if (j < 0) {
    return nan();
  }
  while (j >= 0 && !image_->get(j, centerI) && stateCount[1] <= maxCount) {
    stateCount[1]++;
    j--;
  }
  if (j < 0 || stateCount[1] > maxCount) {
    return nan();
  }
  while (j >= 0 && image_->get(j, centerI) && stateCount[0] <= maxCount) {
    stateCount[0]++;
    j--;
  }
  if (stateCount[0] > maxCount) {
    return nan();
  }

  j = (int)(startJ + 1);
  while (j < maxJ && image_->get(j, centerI)) {
    stateCount[2]++;
    j++;
  }
  if (j == maxJ) {
    return nan();
  }
  while (j < maxJ && !image_->get(j, centerI) && stateCount[3] < maxCount) {
    stateCount[3]++;
    j++;
  }
  if (j == maxJ || stateCount[3] >= maxCount) {
    return nan();
  }
  while (j < maxJ && image_->get(j, centerI) && stateCount[4] < maxCount) {
    stateCount[4]++;
    j++;
  }
  if (stateCount[4] >= maxCount) {
    return nan();
  }

  // If we found a finder-pattern-like section, but its size is significantly different than
  // the original, assume it's a false positive
  int stateCountTotal = stateCount[0] + stateCount[1] + stateCount[2] + stateCount[3] + stateCount[4];
  if (5 * abs(stateCountTotal - originalStateCountTotal) >= originalStateCountTotal) {
    return nan();
  }

  return foundPatternCross(stateCount) ? centerFromEnd(stateCount, j) : nan();
}

bool FinderPatternFinder::handlePossibleCenter(int* stateCount, size_t i, size_t j) {
  int stateCountTotal = stateCount[0] + stateCount[1] + stateCount[2] + stateCount[3] + stateCount[4];
  float centerJ = centerFromEnd(stateCount, (int)j);
  float centerI = crossCheckVertical(i, (size_t)centerJ, stateCount[2], stateCountTotal);
  if (!isnan(centerI)) {
    // Re-cross check
    centerJ = crossCheckHorizontal((size_t)centerJ, (size_t)centerI, stateCount[2], stateCountTotal);
    if (!isnan(centerJ)) {
      float estimatedModuleSize = (float)stateCountTotal / 7.0f;
      bool found = false;
      size_t max = possibleCenters_.size();
      for (size_t index = 0; index < max; index++) {
        Ref<FinderPattern> center = possibleCenters_[index];
        // Look for about the same center and module size:
        if (center->aboutEquals(estimatedModuleSize, centerI, centerJ)) {
          possibleCenters_[index] = center->combineEstimate(centerI, centerJ, estimatedModuleSize);
          found = true;
          break;
        }
      }
      if (!found) {
        Ref<FinderPattern> newPattern(new FinderPattern(centerJ, centerI, estimatedModuleSize));
        possibleCenters_.push_back(newPattern);
        if (callback_ != 0) {
          callback_->foundPossibleResultPoint(*newPattern);
        }
      }
      return true;
    }
  }
  return false;
}

int FinderPatternFinder::findRowSkip() {
  size_t max = possibleCenters_.size();
  if (max <= 1) {
    return 0;
  }
  Ref<FinderPattern> firstConfirmedCenter;
  for (size_t i = 0; i < max; i++) {
    Ref<FinderPattern> center = possibleCenters_[i];
    if (center->getCount() >= CENTER_QUORUM) {
      if (firstConfirmedCenter == 0) {
        firstConfirmedCenter = center;
      } else {
        // We have two confirmed centers
        // How far down can we skip before resuming looking for the next
        // pattern? In the worst case, only the difference between the
        // difference in the x / y coordinates of the two centers.
        // This is the case where you find top left first. Draw it out.
        hasSkipped_ = true;
        return (int)(abs(firstConfirmedCenter->getX() - center->getX()) - abs(firstConfirmedCenter->getY()
                     - center->getY()))/2;
      }
    }
  }
  return 0;
}

bool FinderPatternFinder::haveMultiplyConfirmedCenters() {
  int confirmedCount = 0;
  float totalModuleSize = 0.0f;
  size_t max = possibleCenters_.size();
  for (size_t i = 0; i < max; i++) {
    Ref<FinderPattern> pattern = possibleCenters_[i];
    if (pattern->getCount() >= CENTER_QUORUM) {
      confirmedCount++;
      totalModuleSize += pattern->getEstimatedModuleSize();
    }
  }
  if (confirmedCount < 3) {
    return false;
  }
  // OK, we have at least 3 confirmed centers, but, it's possible that one is a "false positive"
  // and that we need to keep looking. We detect this by asking if the estimated module sizes
  // vary too much. We arbitrarily say that when the total deviation from average exceeds
  // 5% of the total module size estimates, it's too much.
  float average = totalModuleSize / max;
  float totalDeviation = 0.0f;
  for (size_t i = 0; i < max; i++) {
    Ref<FinderPattern> pattern = possibleCenters_[i];
    totalDeviation += abs(pattern->getEstimatedModuleSize() - average);
  }
  return totalDeviation <= 0.05f * totalModuleSize;
}

vector< Ref<FinderPattern> > FinderPatternFinder::selectBestPatterns() {
  size_t startSize = possibleCenters_.size();

  if (startSize < 3) {
    // Couldn't find enough finder patterns
    throw zxing::ReaderException("Could not find three finder patterns");
  }

  // Filter outlier possibilities whose module size is too different
  if (startSize > 3) {
    // But we can only afford to do so if we have at least 4 possibilities to choose from
    float totalModuleSize = 0.0f;
    float square = 0.0f;
    for (size_t i = 0; i < startSize; i++) {
      float size = possibleCenters_[i]->getEstimatedModuleSize();
      totalModuleSize += size;
      square += size * size;
    }
    float average = totalModuleSize / (float) startSize;
    float stdDev = (float)sqrt(square / startSize - average * average);

    sort(possibleCenters_.begin(), possibleCenters_.end(), FurthestFromAverageComparator(average));

    float limit = max(0.2f * average, stdDev);

    for (size_t i = 0; i < possibleCenters_.size() && possibleCenters_.size() > 3; i++) {
      if (abs(possibleCenters_[i]->getEstimatedModuleSize() - average) > limit) {
        possibleCenters_.erase(possibleCenters_.begin()+i);
        i--;
      }
    }
  }

  if (possibleCenters_.size() > 3) {
    // Throw away all but those first size candidate points we found.
    float totalModuleSize = 0.0f;
    for (size_t i = 0; i < possibleCenters_.size(); i++) {
      float size = possibleCenters_[i]->getEstimatedModuleSize();
      totalModuleSize += size;
    }
    float average = totalModuleSize / (float) possibleCenters_.size();
    sort(possibleCenters_.begin(), possibleCenters_.end(), CenterComparator(average));
  }

  if (possibleCenters_.size() > 3) {
    possibleCenters_.erase(possibleCenters_.begin()+3,possibleCenters_.end());
  }

  vector<Ref<FinderPattern> > result(3);
  result[0] = possibleCenters_[0];
  result[1] = possibleCenters_[1];
  result[2] = possibleCenters_[2];
  return result;
}

vector<Ref<FinderPattern> > FinderPatternFinder::orderBestPatterns(vector<Ref<FinderPattern> > patterns) {
  // Find distances between pattern centers
  float abDistance = distance(patterns[0], patterns[1]);
  float bcDistance = distance(patterns[1], patterns[2]);
  float acDistance = distance(patterns[0], patterns[2]);

  Ref<FinderPattern> topLeft;
  Ref<FinderPattern> topRight;
  Ref<FinderPattern> bottomLeft;
  // Assume one closest to other two is top left;
  // topRight and bottomLeft will just be guesses below at first
  if (bcDistance >= abDistance && bcDistance >= acDistance) {
    topLeft = patterns[0];
    topRight = patterns[1];
    bottomLeft = patterns[2];
  } else if (acDistance >= bcDistance && acDistance >= abDistance) {
    topLeft = patterns[1];
    topRight = patterns[0];
    bottomLeft = patterns[2];
  } else {
    topLeft = patterns[2];
    topRight = patterns[0];
    bottomLeft = patterns[1];
  }

  // Use cross product to figure out which of other1/2 is the bottom left
  // pattern. The vector "top-left -> bottom-left" x "top-left -> top-right"
  // should yield a vector with positive z component
  if ((bottomLeft->getY() - topLeft->getY()) * (topRight->getX() - topLeft->getX()) < (bottomLeft->getX()
      - topLeft->getX()) * (topRight->getY() - topLeft->getY())) {
    Ref<FinderPattern> temp = topRight;
    topRight = bottomLeft;
    bottomLeft = temp;
  }

  vector<Ref<FinderPattern> > results(3);
  results[0] = bottomLeft;
  results[1] = topLeft;
  results[2] = topRight;
  return results;
}

float FinderPatternFinder::distance(Ref<ResultPoint> p1, Ref<ResultPoint> p2) {
  float dx = p1->getX() - p2->getX();
  float dy = p1->getY() - p2->getY();
  return (float)sqrt(dx * dx + dy * dy);
}

FinderPatternFinder::FinderPatternFinder(Ref<BitMatrix> image,
                                           Ref<ResultPointCallback>const& callback) :
    image_(image), possibleCenters_(), hasSkipped_(false), callback_(callback) {
}

Ref<FinderPatternInfo> FinderPatternFinder::find(DecodeHints const& hints) {
  bool tryHarder = hints.getTryHarder();

  size_t maxI = image_->getHeight();
  size_t maxJ = image_->getWidth();


  // We are looking for black/white/black/white/black modules in
  // 1:1:3:1:1 ratio; this tracks the number of such modules seen so far

  // As this is used often, we use an integer array instead of vector
  int stateCount[5];
  bool done = false;


  // Let's assume that the maximum version QR Code we support takes up 1/4
  // the height of the image, and then account for the center being 3
  // modules in size. This gives the smallest number of pixels the center
  // could be, so skip this often. When trying harder, look for all
  // QR versions regardless of how dense they are.
  int iSkip = (int)((3 * maxI) / (4 * MAX_MODULES));
  if (iSkip < MIN_SKIP || tryHarder) {
      iSkip = MIN_SKIP;
  }

  // This is slightly faster than using the Ref. Efficiency is important here
  BitMatrix& matrix = *image_;

  for (size_t i = iSkip - 1; i < maxI && !done; i += iSkip) {
    // Get a row of black/white values

    stateCount[0] = 0;
    stateCount[1] = 0;
    stateCount[2] = 0;
    stateCount[3] = 0;
    stateCount[4] = 0;
    int currentState = 0;
    for (size_t j = 0; j < maxJ; j++) {
      if (matrix.get(j, i)) {
        // Black pixel
        if ((currentState & 1) == 1) { // Counting white pixels
          currentState++;
        }
        stateCount[currentState]++;
      } else { // White pixel
        if ((currentState & 1) == 0) { // Counting black pixels
          if (currentState == 4) { // A winner?
            if (foundPatternCross(stateCount)) { // Yes
              bool confirmed = handlePossibleCenter(stateCount, i, j);
              if (confirmed) {
                // Start examining every other line. Checking each line turned out to be too
                // expensive and didn't improve performance.
                iSkip = 2;
                if (hasSkipped_) {
                  done = haveMultiplyConfirmedCenters();
                } else {
                  int rowSkip = findRowSkip();
                  if (rowSkip > stateCount[2]) {
                    // Skip rows between row of lower confirmed center
                    // and top of presumed third confirmed center
                    // but back up a bit to get a full chance of detecting
                    // it, entire width of center of finder pattern

                    // Skip by rowSkip, but back off by stateCount[2] (size
                    // of last center of pattern we saw) to be conservative,
                    // and also back off by iSkip which is about to be
                    // re-added
                    i += rowSkip - stateCount[2] - iSkip;
                    j = maxJ - 1;
                  }
                }
              } else {
                stateCount[0] = stateCount[2];
                stateCount[1] = stateCount[3];
                stateCount[2] = stateCount[4];
                stateCount[3] = 1;
                stateCount[4] = 0;
                currentState = 3;
                continue;
              }
              // Clear state to start looking again
              currentState = 0;
              stateCount[0] = 0;
              stateCount[1] = 0;
              stateCount[2] = 0;
              stateCount[3] = 0;
              stateCount[4] = 0;
            } else { // No, shift counts back by two
              stateCount[0] = stateCount[2];
              stateCount[1] = stateCount[3];
              stateCount[2] = stateCount[4];
              stateCount[3] = 1;
              stateCount[4] = 0;
              currentState = 3;
            }
          } else {
            stateCount[++currentState]++;
          }
        } else { // Counting white pixels
          stateCount[currentState]++;
        }
      }
    }
    if (foundPatternCross(stateCount)) {
      bool confirmed = handlePossibleCenter(stateCount, i, maxJ);
      if (confirmed) {
        iSkip = stateCount[0];
        if (hasSkipped_) {
          // Found a third one
          done = haveMultiplyConfirmedCenters();
        }
      }
    }
  }

  vector<Ref<FinderPattern> > patternInfo = selectBestPatterns();
  patternInfo = orderBestPatterns(patternInfo);

  Ref<FinderPatternInfo> result(new FinderPatternInfo(patternInfo));
  return result;
}

Ref<BitMatrix> FinderPatternFinder::getImage() {
  return image_;
}

vector<Ref<FinderPattern> >& FinderPatternFinder::getPossibleCenters() {
  return possibleCenters_;
}
}
}

// file: zxing/qrcode/detector/FinderPatternInfo.cpp

/*
 *  FinderPatternInfo.cpp
 *  zxing
 *
 *  Created by Christian Brunschen on 13/05/2008.
 *  Copyright 2008 ZXing authors All rights reserved.
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

// #include <zxing/qrcode/detector/FinderPatternInfo.h>

namespace zxing {
namespace qrcode {

FinderPatternInfo::FinderPatternInfo(std::vector<Ref<FinderPattern> > patternCenters) :
    bottomLeft_(patternCenters[0]), topLeft_(patternCenters[1]), topRight_(patternCenters[2]) {
}

Ref<FinderPattern> FinderPatternInfo::getBottomLeft() {
  return bottomLeft_;
}
Ref<FinderPattern> FinderPatternInfo::getTopLeft() {
  return topLeft_;
}
Ref<FinderPattern> FinderPatternInfo::getTopRight() {
  return topRight_;
}

}
}
