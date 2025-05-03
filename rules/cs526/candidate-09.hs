module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule06 :: DSLContext Rewrite
rule06 = do
  rclass <- newRClass "rclass"
  [size, low, high, int] <- newMaps ["size", "low", "high", "int"] rclass
  tX <- newTensor @TensorReal "X" [rclass --> size]
  tY <- newTensor @TensorReal "Y" [rclass --> size]
  let paddingConfig =
        Padding
          { low = [rclass --> low],
            interior = [rclass --> int],
            high = [rclass --> high]
          }
  lhs <-
    numBinOp
      Div
      (pad tX (1 :: TensorReal) paddingConfig)
      (pad tY (1 :: TensorReal) paddingConfig)
  rhs <- pad (numBinOp Div tX tY) (1 :: TensorReal) paddingConfig
  rewrite "Div(Pad(X, val, low, high, int), Pad(Y, val, low, high, int)) ==> Div(Add(X, Y), val, low, high, int) if val = 1" lhs rhs

main :: IO ()
main = do
  print "############################## rule06 ##############################"
  verifyDSL rule06
