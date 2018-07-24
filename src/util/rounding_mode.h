/*********************                                                        */
/*! \file rounding_mode.h
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

#ifndef __CVC4__UTIL__ROUNDING_MODE_H
#define __CVC4__UTIL__ROUNDING_MODE_H

#include <fenv.h>

namespace CVC4 {

/**
 * A concrete instance of the rounding mode sort
 */
enum CVC4_PUBLIC RoundingMode
{
  roundNearestTiesToEven = FE_TONEAREST,
  roundTowardPositive = FE_UPWARD,
  roundTowardNegative = FE_DOWNWARD,
  roundTowardZero = FE_TOWARDZERO,
  // Initializes this to the diagonalization of the 4 other values.
  roundNearestTiesToAway = (((~FE_TONEAREST) & 0x1) | ((~FE_UPWARD) & 0x2)
                            | ((~FE_DOWNWARD) & 0x4) | ((~FE_TOWARDZERO) & 0x8))
}; /* enum RoundingMode */

struct CVC4_PUBLIC RoundingModeHashFunction
{
  inline size_t operator()(const RoundingMode& rm) const { return size_t(rm); }
}; /* struct RoundingModeHashFunction */

}  // namespace CVC4

#endif /* __CVC4__UTIL__ROUNDING_MODE_H */
