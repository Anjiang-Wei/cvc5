#include "util/floatingpoint_mpfr_imp.h"

#include <stdio.h>
#include <iostream>

#include "base/cvc4_assert.h"

namespace CVC4 {

FloatingPoint2::FloatingPoint2(unsigned e, unsigned s, const BitVector &bv)
    : d_size(e, s)
{
  Assert(e + s == bv.getSize());

  // Reset exponent ranges (in case we just did some arithmetic with narrower
  // bit-widths.
  mpfr_set_emax(mpfr_get_emax_max());
  mpfr_set_emin(mpfr_get_emin_min());

  // Set precision to `s`. `s` includes the sign bit, which the MPFR's
  // precision does not count but MPFR's representation does not have a hidden
  // bit, so we end up with `s` bits of precision.
  mpfr_init2(d_val, s);

  int sign = bv.isBitSet(bv.getSize() - 1) ? -1 : 1;
  uint64_t exp =
      bv.extract(bv.getSize() - 2, s - 1).getValue().getUnsignedLong();
  BitVector sig = bv.extract(s - 2, 0);

  uint64_t maxExp = (1 << e) - 1;
  if (exp == maxExp)
  {
    if (sig == BitVector(s - 1))
    {
      // Infinity
      mpfr_set_inf(d_val, sign);
    }
    else
    {
      // NaN
      mpfr_set_nan(d_val);
    }
  }
  else if (exp == 0)
  {
    if (sig == BitVector(s - 1))
    {
      // +/- 0.0
      mpfr_set_zero(d_val, sign);
    }
    else
    {
      // Subnormal values
      std::stringstream ss;
      ss << (sign > 0 ? "" : "-");
      ss << "0.";
      ss << sig.toString(2);
      std::string sigStr = ss.str();
      mpfr_set_str(d_val, sigStr.c_str(), 2, MPFR_RNDD);

      int64_t sigExp = mpfr_get_exp(d_val);

      // Remove the bias from the exponent and add one to adjust for the hidden
      // bit.
      int64_t ubExp = static_cast<int64_t>(exp) - ((1 << (e - 1)) - 1) + 1;
      mpfr_set_exp(d_val, sigExp + ubExp);
    }
  }
  else
  {
    // Normal values
    std::stringstream ss;
    ss << (sign > 0 ? "" : "-");
    ss << "1.";
    ss << sig.toString(2);
    std::string sigStr = ss.str();
    mpfr_set_str(d_val, sigStr.c_str(), 2, MPFR_RNDD);

    // Remove the bias from the exponent and add one to adjust for the hidden
    // bit.
    int64_t ubExp = static_cast<int64_t>(exp) - ((1 << (e - 1)) - 1) + 1;
    mpfr_set_exp(d_val, ubExp);
  }
}

FloatingPoint2::FloatingPoint2(const FloatingPoint2 &fp) : d_size(fp.d_size)
{
  mpfr_init2(d_val, d_size.significand());
  // Rounding mode does not matter since the precision of `this` and `fp` are
  // the same.
  mpfr_set(d_val, fp.d_val, MPFR_RNDN);
}

/*
FloatingPoint::FloatingPoint (const FloatingPointSize &oldt, const
FloatingPointLiteral &oldfpl) : fpl(oldfpl), t(oldt) {}
FloatingPoint::FloatingPoint (const FloatingPoint &fp) : fpl(fp.fpl), t(fp.t) {}
FloatingPoint::FloatingPoint (const FloatingPointSize &ct, const RoundingMode
&rm, const BitVector &bv, bool signedBV); FloatingPoint (const FloatingPointSize
&ct, const RoundingMode &rm, const Rational &r);
*/

FloatingPoint2::~FloatingPoint2() { mpfr_clear(d_val); }

void FloatingPoint2::print() const
{
  // mpfr_out_str(stdout, 10, 0, d_val, MPFR_RNDD);
  mpfr_dump(d_val);
}

FloatingPoint2 FloatingPoint2::plus(const RoundingMode &rm,
                                    const FloatingPoint2 &arg) const
{
  Assert(d_size == arg.d_size);

  mpfr_rnd_t mpfrRm = getMpfrRndMode(rm);

  setExpRange();

  FloatingPoint2 res(d_size.exponent(), d_size.significand());
  int i = mpfr_add(res.d_val, d_val, arg.d_val, mpfrRm);
  mpfr_subnormalize(res.d_val, i, mpfrRm);
  return res;
}

FloatingPoint2 FloatingPoint2::mult(const RoundingMode &rm,
                                    const FloatingPoint2 &arg) const
{
  Assert(d_size == arg.d_size);

  setExpRange();

  FloatingPoint2 res(d_size.exponent(), d_size.significand());
  if (rm == roundNearestTiesToAway)
  {
    int i = mpfr_round_nearest_away(mpfr_mul, res.d_val, d_val, arg.d_val);
    i = mpfr_subnormalize(res.d_val, i, MPFR_RNDNA);
  }
  else
  {
    mpfr_rnd_t mpfrRm = getMpfrRndMode(rm);
    int i = mpfr_mul(res.d_val, d_val, arg.d_val, mpfrRm);
    mpfr_subnormalize(res.d_val, i, mpfrRm);
  }
  return res;
}

FloatingPoint2 FloatingPoint2::div(const RoundingMode &rm,
                                   const FloatingPoint2 &arg) const
{
  Assert(d_size == arg.d_size);

  setExpRange();

  FloatingPoint2 res(d_size.exponent(), d_size.significand());
  if (rm == roundNearestTiesToAway)
  {
    int i = mpfr_round_nearest_away(mpfr_div, res.d_val, d_val, arg.d_val);
    i = mpfr_subnormalize(res.d_val, i, MPFR_RNDNA);
  }
  else
  {
    mpfr_rnd_t mpfrRm = getMpfrRndMode(rm);
    int i = mpfr_div(res.d_val, d_val, arg.d_val, mpfrRm);
    mpfr_subnormalize(res.d_val, i, mpfrRm);
  }
  return res;
}

FloatingPoint2 FloatingPoint2::sqrt(const RoundingMode &rm) const
{
  setExpRange();

  FloatingPoint2 res(d_size.exponent(), d_size.significand());
  if (rm == roundNearestTiesToAway)
  {
    int i = mpfr_round_nearest_away(mpfr_sqrt, res.d_val, d_val);
    i = mpfr_subnormalize(res.d_val, i, MPFR_RNDNA);
  }
  else
  {
    mpfr_rnd_t mpfrRm = getMpfrRndMode(rm);
    int i = mpfr_sqrt(res.d_val, d_val, mpfrRm);
    mpfr_subnormalize(res.d_val, i, mpfrRm);
  }
  return res;
}

bool FloatingPoint2::operator==(const FloatingPoint2 &fp) const
{
  // mpfr_equal_p() considers +0.0 to be equal to -0.0, which is why we also
  // have to make sure that the signs of the floating-point values match.
  return (mpfr_equal_p(d_val, fp.d_val) && (isNegative() == fp.isNegative()))
         || mpfr_unordered_p(d_val, fp.d_val);
}

bool FloatingPoint2::operator!=(const FloatingPoint2 &fp) const
{
  return !(*this == fp);
}

BitVector FloatingPoint2::pack(void) const
{
  // Reset exponent ranges (in case we just did some arithmetic with narrower
  // bit-widths.
  mpfr_set_emax(mpfr_get_emax_max());
  mpfr_set_emin(mpfr_get_emin_min());

  unsigned e = d_size.exponent();
  unsigned s = d_size.significand() - 1;
  unsigned size = e + s;

  if (isNaN())
  {
    return BitVector::mkOnes(size);
  }

  BitVector sign(1, isPositive() ? 0u : 1u);
  BitVector exp;
  BitVector sig;

  if (isZero())
  {
    exp = BitVector(e);
    sig = BitVector(s);
  }
  else if (isInfinite())
  {
    exp = BitVector::mkOnes(e);
    sig = BitVector(s);
  }
  else if (isSubnormal())
  {
    mpfr_exp_t mpfrExp;
    char *str = mpfr_get_str(nullptr, &mpfrExp, 2, s + 1, d_val, MPFR_RNDN);
    exp = BitVector(e);
    std::string sigStr(str + (isNegative() ? 1 : 0));
    sigStr = std::string(getSubnormalThreshold() - mpfrExp, '0') + sigStr;
    sigStr.resize(s, '0');
    sig = BitVector(sigStr, 2);
    mpfr_free_str(str);
  }
  else
  {
    mpfr_exp_t mpfrExp;
    char *str = mpfr_get_str(nullptr, &mpfrExp, 2, s + 1, d_val, MPFR_RNDN);
    exp =
        BitVector(e, static_cast<uint64_t>(mpfrExp + ((1 << (e - 1)) - 1) - 1));
    std::string sigStr(str + 1 + (isNegative() ? 1 : 0));
    sigStr.resize(s, '0');
    sig = BitVector(sigStr, 2);
    mpfr_free_str(str);
  }

  return sign.concat(exp.concat(sig));
}

FloatingPoint2 FloatingPoint2::convert(const FloatingPointSize &target,
                                       const RoundingMode &rm) const
{
  // Reset exponent ranges (in case we just did some arithmetic with narrower
  // bit-widths.
  mpfr_set_emax(mpfr_get_emax_max());
  mpfr_set_emin(mpfr_get_emin_min() + 1);

  FloatingPoint2 res(target.exponent(), target.significand());

  if (rm == roundNearestTiesToAway)
  {
    // mpfr_t tmp;
    // mpfr_init2(tmp, target.significand());
    int i = mpfr_round_nearest_away(mpfr_set, res.d_val, d_val);
    res.setExpRange();
    i = mpfr_round_nearest_away(mpfr_check_range, res.d_val, i);
    // mpfr_round_nearest_away_begin(res.d_val);
    // mpfr_set(res.d_val, tmp, MPFR_RNDN);
    i = mpfr_subnormalize(res.d_val, i, MPFR_RNDNA);
    // mpfr_round_nearest_away_end(res.d_val, i);
  }
  else
  {
    int i = mpfr_set(res.d_val, d_val, getMpfrRndMode(rm));
    res.setExpRange();
    i = mpfr_check_range(res.d_val, i, getMpfrRndMode(rm));
    mpfr_subnormalize(res.d_val, i, getMpfrRndMode(rm));
  }
  return res;
}

/*
static FloatingPoint makeNaN (const FloatingPointSize &t);
static FloatingPoint makeInf (const FloatingPointSize &t, bool sign);
static FloatingPoint makeZero (const FloatingPointSize &t, bool sign);

const FloatingPointLiteral & getLiteral (void) const {
  return this->fpl;
}

// Gives the corresponding IEEE-754 transfer format


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
min/max(-0,+0) or (+0,-0) FloatingPoint maxTotal (const FloatingPoint &arg, bool
zeroCaseLeft) const; FloatingPoint minTotal (const FloatingPoint &arg, bool
zeroCaseLeft) const;

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

FloatingPoint convert (const FloatingPointSize &target, const RoundingMode &rm)
const;

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

FloatingPoint2::FloatingPoint2(unsigned e, unsigned s) : d_size(e, s)
{
  // Set precision to `s`. `s` includes the sign bit, which the MPFR's
  // precision does not count but MPFR's representation does not have a hidden
  // bit, so we end up with `s` bits of precision.
  mpfr_init2(d_val, s);
}

mpfr_rnd_t FloatingPoint2::getMpfrRndMode(const RoundingMode &rm) const
{
  switch (rm)
  {
    case roundNearestTiesToEven: return MPFR_RNDN;
    case roundTowardPositive: return MPFR_RNDU;
    case roundTowardNegative: return MPFR_RNDD;
    case roundTowardZero: return MPFR_RNDZ;
    default:
      IllegalArgument(
          "Rounding mode not supported by MPFR. Note: if you are trying to "
          "round-to-nearest-away, consider using mpfr_round_nearest_away.");
  }
}

void FloatingPoint2::setExpRange() const
{
  mpfr_set_emax(1 << (d_size.exponent() - 1));
  mpfr_set_emin(-static_cast<int64_t>((1 << (d_size.exponent() - 1))
                                      + d_size.significand() - 4));
}

}  // namespace CVC4
