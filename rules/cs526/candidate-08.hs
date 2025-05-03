module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule04 :: forall a. NumRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tP <- newTensor @SymBool "P" [rclass --> map]
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- select tP (numBinOp Add tX tZ) (numBinOp Add tY tZ)
  rhs <- numBinOp Add (select tP tX tY) tZ
  rewrite "Select(P, Add(X, Z), Add(Y, Z)) ==> Add(Select(P, X, Y), Z)" lhs rhs

main :: IO ()
main = do
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
