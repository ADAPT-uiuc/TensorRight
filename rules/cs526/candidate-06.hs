module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "tX" [rclass --> map]
  tY <- newTensor @a "tY" [rclass --> map]
  lhs <- clamp tX tX tY
  let rhs = tX
  rewrite "Clamp(X, X, Y) ⇒ X" lhs rhs

rule01_correct :: forall a. NumRule a
rule01_correct _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "tX" [rclass --> map]
  tY <- newTensor @a "tY" [rclass --> map]
  lhs <- clamp tX tX tY
  rhs <- numBinOp Min tX tY
  rewrite "Clamp(X, X, Y) ⇒ Min(X, Y)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule01_correct ##############################"
  verifyNumDSL rule01_correct
