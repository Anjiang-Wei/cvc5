#include <cxxtest/TestSuite.h>
#include <limits>
#include <sstream>

#include "util/bitvector.h"
#include "util/floatingpoint.h"
#include "util/floatingpoint_mpfr_imp.h"
#include "util/sampler.h"

using namespace CVC4;
using namespace std;

class FloatingPointMpfrImpBlack : public CxxTest::TestSuite
{
 public:
  void setUp()
  {
    two = BitVector("0011101000000000", 2);
    // two = BitVector("010000100000000", 2);
    negOne = BitVector(4, Integer(-1));

    negZero = BitVector("1000000000000000", 2);
    inf = BitVector("0111110000000000", 2);
    negOnePtFive = BitVector("1011111000000000", 2);
    maxNormal = BitVector("0111101111111111", 2);
    maxDenorm = BitVector("0000001111111111", 2);
    minDenorm = BitVector("0000000000000001", 2);
    sMaxDenorm = BitVector("00000000011111111111111111111111", 2);
    sMinDenorm = BitVector("00000000000000000000000000000001", 2);
    sQuarter = BitVector("00111110100000000000000000000000", 2);
    sHalf = BitVector("00111111000000000000000000000000", 2);
  }

  void checkMult(uint32_t a, uint32_t b)
  {
    FloatingPoint2 fpA(8, 24, BitVector(32, a));
    float fA = reinterpret_cast<float&>(a);
    FloatingPoint2 fpB(8, 24, BitVector(32, b));
    float fB = reinterpret_cast<float&>(b);
    FloatingPoint2 fpC = fpA.mult(RoundingMode(), fpB);
    float fC = fA * fB;
    uint32_t iC = reinterpret_cast<uint32_t&>(fC);
    FloatingPoint2 fpExpectedC(8, 24, BitVector(32, iC));
    std::cout << "COMPARING" << std::endl;
    std::cout << "---------" << std::endl;
    fpC.print();
    std::cout << std::endl << "---------" << std::endl;
    fpExpectedC.print();
    std::cout << std::endl << "---------" << std::endl;
    std::cout << fC << std::endl;
    std::cout << "---------" << std::endl;
    std::cout << (fpC == fpExpectedC) << std::endl;
    TS_ASSERT_EQUALS(fpC, fpExpectedC);
  }

  void testInit()
  {
    BitVector bvNegZero(16, static_cast<uint32_t>(0b1000000000000000));
    BitVector bvPosZero(16, static_cast<uint32_t>(0b0000000000000000));
    FloatingPoint2 fpNegZero(5, 11, bvNegZero);
    FloatingPoint2 fpPosZero(5, 11, bvPosZero);
    // TS_ASSERT_DIFFERS(fpNegZero, fpPosZero);

    FloatingPoint2 fpInf(5, 11, inf);
    std::cout << std::endl << "----" << std::endl;
    fpInf.print();
    std::cout << std::endl << "----" << std::endl;
    std::cout << std::endl << "----" << std::endl;
    fpNegZero.print();
    std::cout << std::endl << "----" << std::endl;
    FloatingPoint2 fpNegOnePtFive(5, 11, negOnePtFive);
    std::cout << std::endl << "----" << std::endl;
    fpNegOnePtFive.print();
    std::cout << std::endl << "----" << std::endl;
    FloatingPoint2 fpNegThree =
        fpNegOnePtFive.plus(RoundingMode(), fpNegOnePtFive);
    std::cout << std::endl << "----" << std::endl;
    fpNegThree.print();
    std::cout << std::endl << "----" << std::endl;
    std::cout << std::endl << "----" << std::endl;
    FloatingPoint2 fpMaxNormal(5, 11, maxNormal);
    std::cout << std::endl << "----" << std::endl;
    fpMaxNormal.print();
    std::cout << std::endl << "----" << std::endl;
    fpMaxNormal.plus(RoundingMode(), fpMaxNormal).print();
    std::cout << std::endl << "----" << std::endl;

    FloatingPoint2 fpMaxDenorm(5, 11, maxDenorm);
    std::cout << std::endl << "----" << std::endl;
    fpMaxDenorm.print();
    std::cout << std::endl << "----" << std::endl;

    FloatingPoint2 fpMinDenorm(5, 11, minDenorm);
    std::cout << std::endl << "----" << std::endl;
    fpMinDenorm.print();
    std::cout << std::endl << "----" << std::endl;

    FloatingPoint2 fpSMaxDenorm(8, 24, sMaxDenorm);
    std::cout << std::endl << "----" << std::endl;
    fpSMaxDenorm.print();
    std::cout << std::endl << "----" << std::endl;

    FloatingPoint2 fpSMinDenorm(8, 24, sMinDenorm);
    std::cout << std::endl << "----" << std::endl;
    fpSMinDenorm.print();
    std::cout << std::endl << "----" << std::endl;

    std::cout << std::endl << "----" << std::endl;
    fpSMinDenorm.mult(RoundingMode(), fpSMinDenorm).print();
    std::cout << std::endl << "----" << std::endl;

    FloatingPoint2 fpSQuarter(8, 24, sQuarter);
    std::cout << std::endl << "----" << std::endl;
    fpSQuarter.print();
    std::cout << std::endl << "----" << std::endl;

    std::cout << std::endl << "----" << std::endl;
    fpSMinDenorm.mult(RoundingMode(), fpSQuarter).print();
    std::cout << std::endl << "----" << std::endl;

    FloatingPoint2 fpSHalf(8, 24, sHalf);
    std::cout << std::endl << "----" << std::endl;
    fpSHalf.print();
    std::cout << std::endl << "----" << std::endl;

    std::cout << std::endl << "----" << std::endl;
    fpSMaxDenorm.mult(RoundingMode(), fpSQuarter).print();
    std::cout << std::endl << "----" << std::endl;

    uint32_t bQuarter = 0b00111110100000000000000000000000;
    uint32_t bMaxDenorm = 0b00000000011111111111111111111111;
    float fMaxDenorm = reinterpret_cast<float&>(bMaxDenorm);

    float fQuarter = 0.25f;

    float fRes = fMaxDenorm * fQuarter;
    uint32_t bRes = reinterpret_cast<uint32_t&>(fRes);
    std::cout << fMaxDenorm << std::endl;
    std::cout << fRes << std::endl;
    std::cout << bRes << std::endl;

    checkMult(bMaxDenorm, bQuarter);

    std::cout << "ASDFASDFASDFASDFASDFSDAFASDFAS" << std::endl;
  }

  void testInitAndPack()
  {
    /*
    FloatingPointSize qs(5, 9);
    for(size_t i = 0; i < std::numeric_limits<uint16_t>::max(); i++) {
      BitVector bv(16, i);
        FloatingPoint fp(5, 11, bv);
        FloatingPoint2 fp2(5, 11, bv);
        if (!fp.isNaN()) {
          TS_ASSERT_EQUALS(fp.pack(), fp2.pack());
        }
        TS_ASSERT_EQUALS(fp.isNaN(), fp2.isNaN());
        TS_ASSERT_EQUALS(fp.isSubnormal(), fp2.isSubnormal());
        TS_ASSERT_EQUALS(fp.isNormal(), fp2.isNormal());
        TS_ASSERT_EQUALS(fp.isPositive(), fp2.isPositive());
        TS_ASSERT_EQUALS(fp.isNegative(), fp2.isNegative());

       FloatingPoint qFp = fp.convert(qs, roundNearestTiesToAway);
       FloatingPoint2 qFp2 = fp2.convert(qs, roundNearestTiesToAway);
        if (!qFp.isNaN()) {
          TS_ASSERT_EQUALS(qFp.pack(), qFp2.pack());
          if (qFp.pack() != qFp2.pack()) {
            std::cout << fp.pack() << std::endl;
            std::cout << qFp.pack() << std::endl;
            std::cout << fp2.pack() << std::endl;
            std::cout << qFp2.pack() << std::endl;
            qFp2.print();
            std::cout << std::endl;
          }
        }
        TS_ASSERT_EQUALS(qFp.isNaN(), qFp2.isNaN());
    }
    */
  }

  void testPlus()
  {
    /*
    for(size_t i = 0; i < 256; i++) {
      for(size_t j = 0; j < 256; j++) {
        FloatingPoint fpA(3, 5, BitVector(8, i));
        FloatingPoint fpB(3, 5, BitVector(8, j));
        FloatingPoint2 fp2A(3, 5, BitVector(8, i));
        FloatingPoint2 fp2B(3, 5, BitVector(8, j));
        FloatingPoint fpRes = fpA.plus(roundNearestTiesToEven, fpB);
        FloatingPoint2 fp2Res = fp2A.plus(roundNearestTiesToEven, fp2B);
        if (fpRes.isNaN()) {
          TS_ASSERT_EQUALS(fpRes.isNaN(), fp2Res.isNaN());
        } else {
          TS_ASSERT_EQUALS(fpRes.pack(), fp2Res.pack());
        }
      }
    }
    */
  }

  void testMul()
  {
    /*
      for(size_t i = 0; i < 256; i++) {
        for(size_t j = 0; j < 256; j++) {
          FloatingPoint fpA(3, 5, BitVector(8, i));
          FloatingPoint fpB(3, 5, BitVector(8, j));
          FloatingPoint2 fp2A(3, 5, BitVector(8, i));
          FloatingPoint2 fp2B(3, 5, BitVector(8, j));
          FloatingPoint fpResMult = fpA.mult(roundNearestTiesToAway, fpB);
          FloatingPoint2 fp2ResMult = fp2A.mult(roundNearestTiesToAway, fp2B);
          if (fpResMult.isNaN()) {
            TS_ASSERT_EQUALS(fpResMult.isNaN(), fp2ResMult.isNaN());
          } else {
            TS_ASSERT_EQUALS(fpResMult.pack(), fp2ResMult.pack());
            if (fpResMult.pack() != fp2ResMult.pack()) {
              std::cout << fpA << std::endl;
              std::cout << fpB << std::endl;
              std::cout << fpResMult.pack() << std::endl;
              std::cout << fp2ResMult.pack() << std::endl;
            }
          }
        }
      */
  }

  void testDiv()
  {
    /*
    for(size_t i = 0; i < 10000; i++) {
      FloatingPoint fpA = Sampler::pickFpBiased(5, 11);
      FloatingPoint fpB = Sampler::pickFpBiased(5, 11);
      FloatingPoint2 fp2A(5, 11, fpA.pack());
      FloatingPoint2 fp2B(5, 11, fpB.pack());
      FloatingPoint fpResDiv = fpA.div(roundNearestTiesToAway, fpB);
      FloatingPoint2 fp2ResDiv = fp2A.div(roundNearestTiesToAway, fp2B);
      if (fpResDiv.isNaN()) {
        TS_ASSERT_EQUALS(fpResDiv.isNaN(), fp2ResDiv.isNaN());
      } else {
        TS_ASSERT_EQUALS(fpResDiv.pack(), fp2ResDiv.pack());
        if (fpResDiv.pack() != fp2ResDiv.pack()) {
          std::cout << fpA << std::endl;
          std::cout << fpB << std::endl;
          std::cout << fpResDiv.pack() << std::endl;
          std::cout << fp2ResDiv.pack() << std::endl;
        }
      }
    }
    */
  }

  void testSqrt()
  {
    for (size_t i = 0; i < 10000; i++)
    {
      FloatingPoint fpA = Sampler::pickFpBiased(5, 11);
      FloatingPoint2 fp2A(5, 11, fpA.pack());
      FloatingPoint fpResMult = fpA.sqrt(roundNearestTiesToAway);
      FloatingPoint2 fp2ResMult = fp2A.sqrt(roundNearestTiesToAway);
      if (fpResMult.isNaN())
      {
        TS_ASSERT_EQUALS(fpResMult.isNaN(), fp2ResMult.isNaN());
      }
      else
      {
        TS_ASSERT_EQUALS(fpResMult.pack(), fp2ResMult.pack());
        if (fpResMult.pack() != fp2ResMult.pack())
        {
          std::cout << fpA << std::endl;
          std::cout << fpResMult.pack() << std::endl;
          std::cout << fp2ResMult.pack() << std::endl;
        }
      }
    }
  }

 private:
  BitVector negZero;
  BitVector one;
  BitVector two;
  BitVector negOne;
  BitVector inf;
  BitVector negOnePtFive;
  BitVector maxNormal;
  BitVector maxDenorm;
  BitVector minDenorm;
  BitVector sMaxDenorm;
  BitVector sMinDenorm;
  BitVector sQuarter;
  BitVector sHalf;
};
