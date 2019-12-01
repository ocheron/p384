{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module KAT_PubKey.P384 (tests) where

import qualified Crypto.PubKey.ECC.Types as ECC
import qualified Crypto.PubKey.ECC.Prim as ECC
import qualified Crypto.PubKey.ECC.P384 as P384

import           Data.ByteArray (Bytes)
import           Crypto.Number.Serialize (i2ospOf, os2ip)
import           Crypto.Number.ModArithmetic (inverseCoprimes)
import           Crypto.Error

import           Imports

newtype P384Scalar = P384Scalar Integer
    deriving (Show,Eq,Ord)

instance Arbitrary P384Scalar where
    -- Cover the full range up to 2^384-1 except 0 and curveN.  To test edge
    -- cases with arithmetic functions, some values close to 0, curveN and
    -- 2^384 are given higher frequency.
    arbitrary = P384Scalar <$> oneof
        [ choose (1, w)
        , choose (w + 1, curveN - w - 1)
        , choose (curveN - w, curveN - 1)
        , choose (curveN + 1, curveN + w)
        , choose (curveN + w + 1, high - w - 1)
        , choose (high - w, high - 1)
        ]
      where high = 2^(384 :: Int)
            w    = 100

curve  = ECC.getCurveByName ECC.SEC_p384r1
curveN = ECC.ecc_n . ECC.common_curve $ curve
curveGen = ECC.ecc_g . ECC.common_curve $ curve

pointP384ToECC :: P384.Point -> ECC.Point
pointP384ToECC = uncurry ECC.Point . P384.pointToIntegers

i2ospScalar :: Integer -> Bytes
i2ospScalar i =
    case i2ospOf 48 i of
        Nothing -> error "invalid size of P384 scalar"
        Just b  -> b

unP384Scalar :: P384Scalar -> P384.Scalar
unP384Scalar (P384Scalar r) =
    let rBytes = i2ospScalar r
     in case P384.scalarFromBinary rBytes of
                    CryptoFailed err    -> error ("cannot convert scalar: " ++ show err)
                    CryptoPassed scalar -> scalar

unP384 :: P384Scalar -> Integer
unP384 (P384Scalar r) = r

modP384Scalar :: P384Scalar -> P384Scalar
modP384Scalar (P384Scalar r) = P384Scalar (r `mod` curveN)

p384ScalarToInteger :: P384.Scalar -> Integer
p384ScalarToInteger s = os2ip (P384.scalarToBinary s :: Bytes)

xS = 0x283c1d7365ce4788f29f8ebf234edffead6fe997fbea5ffa2d58cc9dfa7b1c508b05526f55b9ebb2040f05b48fb6d0e1
yS = 0x9475c99061e41b88ba52efdb8c1690471a61d867ed799729d9c92cd01dbd225630d84ede32a78f9e64664cdac512ef8c
xT = 0x099056e27da7b998da1eeec2904816c57fe935ed5837c37456c9fd14892d3f8c4749b66e3afb81d626356f3b55b4ddd8
yT = 0x2e4c0c234e30ab96688505544ac5e0396fc4eed8dfc363fd43ff93f41b52a3255466d51263aaff357d5dba8138c5e0bb
xR = 0xdfb1fe3a40f7ac9b64c41d39360a7423828b97cb088a4903315e402a7089fa0f8b6c2355169cc9c99dfb44692a9b93dd
yR = 0x453aca1243b5ec6b423a68a25587e1613a634c1c42d2ee7e6c57f449a1c91dc89168b7036ec0a7f37a366185233ec522

tests = testGroup "P384"
    [ testGroup "scalar"
        [ testProperty "marshalling" $ \(QAInteger r) ->
            let rBytes = i2ospScalar r
             in case P384.scalarFromBinary rBytes of
                    CryptoFailed err    -> error (show err)
                    CryptoPassed scalar -> rBytes `propertyEq` P384.scalarToBinary scalar
        , testProperty "add" $ \r1 r2 ->
            let r = (unP384 r1 + unP384 r2) `mod` curveN
                r' = P384.scalarAdd (unP384Scalar r1) (unP384Scalar r2)
             in r `propertyEq` p384ScalarToInteger r'
        , testProperty "add0" $ \r ->
            let v = unP384 r `mod` curveN
                v' = P384.scalarAdd (unP384Scalar r) P384.scalarZero
             in v `propertyEq` p384ScalarToInteger v'
        , testProperty "sub" $ \r1 r2 ->
            let r = (unP384 r1 - unP384 r2) `mod` curveN
                r' = P384.scalarSub (unP384Scalar r1) (unP384Scalar r2)
                v = (unP384 r2 - unP384 r1) `mod` curveN
                v' = P384.scalarSub (unP384Scalar r2) (unP384Scalar r1)
             in propertyHold
                    [ eqTest "r1-r2" r (p384ScalarToInteger r')
                    , eqTest "r2-r1" v (p384ScalarToInteger v')
                    ]
        , testProperty "sub0" $ \r ->
            let v = unP384 r `mod` curveN
                v' = P384.scalarSub (unP384Scalar r) P384.scalarZero
             in v `propertyEq` p384ScalarToInteger v'
        , testProperty "mul" $ \r1 r2 ->
            let r = (unP384 r1 * unP384 r2) `mod` curveN
                r' = P384.scalarMul (unP384Scalar r1) (unP384Scalar r2)
             in r `propertyEq` p384ScalarToInteger r'
        , testProperty "inv" $ \r' ->
            let inv  = inverseCoprimes (unP384 r') curveN
                inv' = P384.scalarInv (unP384Scalar r')
             in if unP384 r' == 0 then True else inv `propertyEq` p384ScalarToInteger inv'
        ]
    , testGroup "point"
        [ testProperty "marshalling" $ \rx ry ->
            let p = P384.pointFromIntegers (unP384 rx, unP384 ry)
                b = P384.pointToBinary p :: Bytes
                p' = P384.unsafePointFromBinary b
             in propertyHold [ eqTest "point" (CryptoPassed p) p' ]
        , testProperty "marshalling-integer" $ \rx ry ->
            let p = P384.pointFromIntegers (unP384 rx, unP384 ry)
                (x,y) = P384.pointToIntegers p
             in propertyHold [ eqTest "x" (unP384 rx) x, eqTest "y" (unP384 ry) y ]
        , testCase "valid-point-1" $ casePointIsValid (xS,yS)
        , testCase "valid-point-2" $ casePointIsValid (xR,yR)
        , testCase "valid-point-3" $ casePointIsValid (xT,yT)
        , testCase "point-add-1" $
            let s = P384.pointFromIntegers (xS, yS)
                t = P384.pointFromIntegers (xT, yT)
                r = P384.pointFromIntegers (xR, yR)
             in r @=? P384.pointAdd s t
        , testProperty "lift-to-curve" propertyLiftToCurve
        , testProperty "point-add" propertyPointAdd
        , testProperty "point-negate" propertyPointNegate
        , testProperty "point-mul" propertyPointMul
        ]
    ]
  where
    casePointIsValid pointTuple =
        let s = P384.pointFromIntegers pointTuple in True @=? P384.pointIsValid s

    propertyLiftToCurve r =
        let p     = P384.toPoint (unP384Scalar r)
            (x,y) = P384.pointToIntegers p
            pEcc  = ECC.pointMul curve (unP384 r) curveGen
         in pEcc `propertyEq` ECC.Point x y

    propertyPointAdd r1 r2 =
        let p1    = P384.toPoint (unP384Scalar r1)
            p2    = P384.toPoint (unP384Scalar r2)
            pe1   = ECC.pointMul curve (unP384 r1) curveGen
            pe2   = ECC.pointMul curve (unP384 r2) curveGen
            pR    = P384.toPoint (P384.scalarAdd (unP384Scalar r1) (unP384Scalar r2))
            peR   = ECC.pointAdd curve pe1 pe2
         in (unP384 r1 + unP384 r2) `mod` curveN /= 0 ==>
            propertyHold [ eqTest "p384" pR (P384.pointAdd p1 p2)
                         , eqTest "ecc" peR (pointP384ToECC pR)
                         ]

    propertyPointNegate r =
        let p  = P384.toPoint (unP384Scalar r)
            pe = ECC.pointMul curve (unP384 r) curveGen
            pR = P384.pointNegate p
         in ECC.pointNegate curve pe `propertyEq` pointP384ToECC pR

    propertyPointMul s' r' =
        let s     = modP384Scalar s'
            r     = modP384Scalar r'
            p     = P384.toPoint (unP384Scalar r)
            pe    = ECC.pointMul curve (unP384 r) curveGen
            pR    = P384.toPoint (P384.scalarMul (unP384Scalar s) (unP384Scalar r))
            peR   = ECC.pointMul curve (unP384 s) pe
         in propertyHold [ eqTest "p384" pR (P384.pointMul (unP384Scalar s) p)
                         , eqTest "ecc" peR (pointP384ToECC pR)
                         ]
