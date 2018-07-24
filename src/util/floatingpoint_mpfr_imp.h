#include "cvc4_public.h"

#ifndef __CVC4__FLOATINGPOINT_MPFR_IMP_H
#define __CVC4__FLOATINGPOINT_MPFR_IMP_H

#define MPFR_USE_C99_FEATURE 1
#include <mpfr.h>
#include <string>

#include "util/bitvector.h"
#include "util/floatingpoint_size.h"
#include "util/rounding_mode.h"

namespace CVC4 {

class CVC4_PUBLIC FloatingPoint2
{
 public:
  FloatingPoint2(unsigned e, unsigned s, const BitVector &bv);
  FloatingPoint2(const FloatingPoint2 &fp);
  ~FloatingPoint2();

  FloatingPoint2 plus(const RoundingMode &rm, const FloatingPoint2 &arg) const;
  FloatingPoint2 mult(const RoundingMode &rm, const FloatingPoint2 &arg) const;
  FloatingPoint2 div(const RoundingMode &rm, const FloatingPoint2 &arg) const;
  FloatingPoint2 sqrt(const RoundingMode &rm) const;

  bool operator==(const FloatingPoint2 &fp) const;
  bool operator!=(const FloatingPoint2 &fp) const;

  // Gives the corresponding IEEE-754 transfer format
  BitVector pack(void) const;

  /**
   * Returns true if the floating-point value is normal (i.e. not subnormal and
   * not any special value) and false otherwise.
   */
  bool isNormal(void) const
  {
    return !isZero() && mpfr_number_p(d_val) != 0
           && mpfr_get_exp(d_val)
                  > -static_cast<int64_t>((1 << (d_size.exponent() - 1)) - 2);
  }

  /**
   * Returns true if the floating-point value is subnormal and false otherwise.
   */
  bool isSubnormal(void) const
  {
    return !isZero() && mpfr_number_p(d_val) != 0
           && mpfr_get_exp(d_val) <= getSubnormalThreshold();
  }

  /**
   * Returns true if the floating-point value is positive or negative zero and
   * false otherwise.
   */
  bool isZero(void) const { return mpfr_zero_p(d_val) != 0; }

  /**
   * Returns true if the floating-point value is positive or negative infinity
   * and false otherwise.
   */
  bool isInfinite(void) const { return mpfr_inf_p(d_val) != 0; }

  /**
   * Returns true if the floating-point value is NaN and false otherwise.
   */
  bool isNaN(void) const { return mpfr_nan_p(d_val) != 0; }

  /**
   * Returns true if the floating-point value is negative and false otherwise.
   * NaN is never negative.
   */
  bool isNegative(void) const { return !isNaN() && mpfr_signbit(d_val) != 0; }

  /**
   * Returns true if the floating-point value is positive and false otherwise.
   * NaN is never positive.
   */
  bool isPositive(void) const { return !isNaN() && mpfr_signbit(d_val) == 0; }

  /**
   * Converts a floating-point value to a value with a different exponent- and
   * signficand size.
   */
  FloatingPoint2 convert(const FloatingPointSize &target,
                         const RoundingMode &rm) const;

  /*
  FloatingPoint (const FloatingPointSize &oldt, const FloatingPointLiteral
  &oldfpl) : fpl(oldfpl), t(oldt) {} FloatingPoint (const FloatingPoint &fp) :
  fpl(fp.fpl), t(fp.t) {} FloatingPoint (const FloatingPointSize &ct, const
  RoundingMode &rm, const BitVector &bv, bool signedBV); FloatingPoint (const
  FloatingPointSize &ct, const RoundingMode &rm, const Rational &r);

  static FloatingPoint makeNaN (const FloatingPointSize &t);
  static FloatingPoint makeInf (const FloatingPointSize &t, bool sign);
  static FloatingPoint makeZero (const FloatingPointSize &t, bool sign);

  const FloatingPointLiteral & getLiteral (void) const {
    return this->fpl;
  }



  FloatingPoint absolute (void) const;
  FloatingPoint negate (void) const;
  FloatingPoint plus (const RoundingMode &rm, const FloatingPoint &arg) const;
  FloatingPoint sub (const RoundingMode &rm, const FloatingPoint &arg) const;
  FloatingPoint mult (const RoundingMode &rm, const FloatingPoint &arg) const;
  FloatingPoint div (const RoundingMode &rm, const FloatingPoint &arg) const;
  FloatingPoint fma (const RoundingMode &rm, const FloatingPoint &arg1, const
  FloatingPoint &arg2) const; FloatingPoint sqrt (const RoundingMode &rm) const;
  FloatingPoint rti (const RoundingMode &rm) const;
  FloatingPoint rem (const FloatingPoint &arg) const;

  // zeroCase is whether the left or right is returned in the case of
  min/max(-0,+0) or (+0,-0) FloatingPoint maxTotal (const FloatingPoint &arg,
  bool zeroCaseLeft) const; FloatingPoint minTotal (const FloatingPoint &arg,
  bool zeroCaseLeft) const;

  // These detect when the answer is defined
  typedef std::pair<FloatingPoint, bool> PartialFloatingPoint;

  PartialFloatingPoint max (const FloatingPoint &arg) const;
  PartialFloatingPoint min (const FloatingPoint &arg) const;


  bool operator ==(const FloatingPoint& fp) const;
  bool operator <= (const FloatingPoint &arg) const;
  bool operator < (const FloatingPoint &arg) const;

  bool isNormal (void) const;
  bool isSubnormal (void) const;
  bool isZero (void) const;
  bool isInfinite (void) const;
  bool isNaN (void) const;
  bool isNegative (void) const;
  bool isPositive (void) const;

  FloatingPoint convert (const FloatingPointSize &target, const RoundingMode
  &rm) const;

  // These require a value to return in the undefined case
  BitVector convertToBVTotal (BitVectorSize width, const RoundingMode &rm,
      bool signedBV, BitVector undefinedCase) const;
  Rational convertToRationalTotal (Rational undefinedCase) const;

  // These detect when the answer is defined
  typedef std::pair<BitVector, bool> PartialBitVector;
  typedef std::pair<Rational, bool> PartialRational;

  PartialBitVector convertToBV (BitVectorSize width, const RoundingMode &rm,
      bool signedBV) const;
  PartialRational convertToRational (void) const;
  */

  void print() const;

 private:
  FloatingPoint2(unsigned e, unsigned s);

  mpfr_rnd_t getMpfrRndMode(const RoundingMode &rm) const;
  int64_t getSubnormalThreshold() const
  {
    return -static_cast<int64_t>((1 << (d_size.exponent() - 1)) - 2);
  }

  void setExpRange() const;

  FloatingPointSize d_size;
  mpfr_t d_val;
}; /* class FloatingPoint */

}  // namespace CVC4

#endif
