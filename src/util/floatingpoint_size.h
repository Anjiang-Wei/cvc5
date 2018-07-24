/*********************                                                        */
/*! \file floatingpoint.h.in
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Tim King, Andres Noetzli
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Utility functions for working with floating point theories. ]]
 **
 ** [[ This file contains the data structures used by the constant and
 **    parametric types of the floating point theory. ]]
 **/

#include "cvc4_public.h"

#ifndef __CVC4__UTIL__FLOATINGPOINT_SIZE_H
#define __CVC4__UTIL__FLOATINGPOINT_SIZE_H

namespace CVC4 {

// Inline these!
inline bool CVC4_PUBLIC validExponentSize(unsigned e) { return e >= 2; }
inline bool CVC4_PUBLIC validSignificandSize(unsigned s) { return s >= 2; }

/**
 * Floating point sorts are parameterised by two non-zero constants
 * giving the width (in bits) of the exponent and significand
 * (including the hidden bit).
 */
class CVC4_PUBLIC FloatingPointSize
{
  /*
    Class invariants:
    * VALIDEXPONENTSIZE(e)
    * VALIDSIGNIFCANDSIZE(s)
   */

 public:
  FloatingPointSize(unsigned _e, unsigned _s);
  FloatingPointSize(const FloatingPointSize& old);

  inline unsigned exponent(void) const { return this->e; }

  inline unsigned significand(void) const { return this->s; }

  bool operator==(const FloatingPointSize& fps) const
  {
    return (e == fps.e) && (s == fps.s);
  }

  // Implement the interface that symfpu uses for floating-point formats.
  inline unsigned exponentWidth(void) const { return this->exponent(); }
  inline unsigned significandWidth(void) const { return this->significand(); }
  inline unsigned packedWidth(void) const
  {
    return this->exponentWidth() + this->significandWidth();
  }
  inline unsigned packedExponentWidth(void) const
  {
    return this->exponentWidth();
  }
  inline unsigned packedSignificandWidth(void) const
  {
    return this->significandWidth() - 1;
  }

 private:
  unsigned e;
  unsigned s;
}; /* class FloatingPointSize */

struct CVC4_PUBLIC FloatingPointSizeHashFunction
{
  static inline size_t ROLL(size_t X, size_t N)
  {
    return (((X) << (N)) | ((X) >> (8 * sizeof((X)) - (N))));
  }

  inline size_t operator()(const FloatingPointSize& fpt) const
  {
    return size_t(ROLL(fpt.exponent(), 4 * sizeof(unsigned))
                  | fpt.significand());
  }
}; /* struct FloatingPointSizeHashFunction */

inline std::ostream& operator<<(std::ostream& os,
                                const FloatingPointSize& fps) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const FloatingPointSize& fps)
{
  return os << "(_ FloatingPoint " << fps.exponent() << " " << fps.significand()
            << ")";
}

}  // namespace CVC4

#endif /* __CVC4__UTIL__FLOATINGPOINT_SIZE_H */
