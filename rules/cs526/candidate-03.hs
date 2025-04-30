module Main (main) where

import Control.Monad.Except (runExceptT)
import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.Core.Tensor.TensorInt (tensorValNe)

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- numUnaryOp Neg (numBinOp Mul (numUnaryOp Neg tX) tY)
  rhs <- numBinOp Mul tX tY
  rewrite "Neg(Mul(Neg(X), Y)) ==> Mul(X, Y)" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  [size, low, high, int] <- newMaps ["size", "low", "high", "int"] rclass
  tX <- newTensor @a "X" [rclass --> size]
  tY <- newTensor @a "Y" [rclass --> size]
  let paddingConfig =
        Padding
          { low = [rclass --> low],
            interior = [rclass --> int],
            high = [rclass --> high]
          }
  lhs <-
    numBinOp
      Add
      (pad tX ("a" :: a) paddingConfig)
      (pad tY ("a" :: a) paddingConfig)
  rhs <- pad (numBinOp Add tX tY) ("a" :: a) paddingConfig
  rewrite "Add(Pad(X, val, low, high, int), Pad(Y, val, low, high, int)) ==> Pad(Add(X, Y), val, low, high, int)" lhs rhs

rule02_correct :: forall a. NumRule a
rule02_correct _ = do
  rclass <- newRClass "rclass"
  [size, low, high, int] <- newMaps ["size", "low", "high", "int"] rclass
  tX <- newTensor @a "X" [rclass --> size]
  tY <- newTensor @a "Y" [rclass --> size]
  let paddingConfig =
        Padding
          { low = [rclass --> low],
            interior = [rclass --> int],
            high = [rclass --> high]
          }
  lhs <-
    numBinOp
      Add
      (pad tX (0 :: a) paddingConfig)
      (pad tY (0 :: a) paddingConfig)
  rhs <- pad (numBinOp Add tX tY) (0 :: a) paddingConfig
  rewrite "Add(Pad(X, val, low, high, int), Pad(Y, val, low, high, int)) ==> Pad(Add(X, Y), val, low, high, int) if val = 0" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  [size, low, high, int] <- newMaps ["size", "low", "high", "int"] rclass
  tX <- newTensor @a "X" [rclass --> size]
  tY <- newTensor @a "Y" [rclass --> size]
  let paddingConfig =
        Padding
          { low = [rclass --> low],
            interior = [rclass --> int],
            high = [rclass --> high]
          }
  lhs <-
    numBinOp
      Mul
      (pad tX ("a" :: a) paddingConfig)
      (pad tY ("a" :: a) paddingConfig)
  rhs <- pad (numBinOp Mul tX tY) ("a" :: a) paddingConfig
  rewrite "Mul(Pad(X, val, low, high, int), Pad(Y, val, low, high, int)) ==> Pad(Mul(X, Y), val, low, high, int)" lhs rhs

rule03_correct :: forall a. NumRule a
rule03_correct _ = do
  rclass <- newRClass "rclass"
  [size, low, high, int] <- newMaps ["size", "low", "high", "int"] rclass
  tX <- newTensor @a "X" [rclass --> size]
  tY <- newTensor @a "Y" [rclass --> size]
  let paddingConfig =
        Padding
          { low = [rclass --> low],
            interior = [rclass --> int],
            high = [rclass --> high]
          }
  lhs <-
    numBinOp
      Mul
      (pad tX (1 :: a) paddingConfig)
      (pad tY (1 :: a) paddingConfig)
  rhs <- pad (numBinOp Mul tX tY) (1 :: a) paddingConfig
  -- TODO: allow adding scalar preconditions
  rewrite "Mul(Pad(X, val, low, high, int), Pad(Y, val, low, high, int)) ==> Pad(Mul(X, Y), val, low, high, int) if val = 0 || val = 1" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  tX <- newTensor @a "X" [rclass --> map]
  lhs <- clamp (numBinOp Min tA tB) tX (numBinOp Max tA tB)
  rhs <- clamp tA tX tB
  rewrite "Clamp(Min(A, B), X, Max(A, B)) ==> Clamp(A, X, B)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule02_correct ##############################"
  verifyNumDSL rule02_correct
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule03_correct ##############################"
  verifyNumDSL rule03_correct
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
