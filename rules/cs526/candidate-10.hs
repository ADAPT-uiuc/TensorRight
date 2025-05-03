module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  tE <- newTensor @a "E" [rclass --> map]
  tMin <- numBinOp Min (numBinOp Add tX tY) tZ
  tMax <- numBinOp Max (numBinOp Add tX tY) tZ
  lhs <- clamp tMin tE tMax
  rhs <- clamp tE (numBinOp Add tX tY) tZ
  rewrite "Clamp(Min(Add(X, Y), E, Max(Add(X, Y), Z)) ==> Clamp(E, Add(X, Y), Z)" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  tW <- newTensor @a "W" [rclass --> map]
  lhs <- clamp (numBinOp Add tX tW) (numBinOp Add tY tW) (numBinOp Add tZ tW)
  rhs <- numBinOp Add (clamp tX tY tZ) tW
  rewrite "Clamp(Add(X, W), Add(Y, W), Add(Z, W)) ==> Add(Clamp(X, Y, Z), W)" lhs rhs

rule02_v1 :: forall a. NumRule a
rule02_v1 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  tW <- newTensor @a "W" [rclass --> map]
  lhs <- clamp (numBinOp Mul tX tW) (numBinOp Mul tY tW) (numBinOp Mul tZ tW)
  rhs <- numBinOp Mul (clamp tX tY tZ) tW
  rewrite "Clamp(Mul(X, W), Mul(Y, W), Mul(Z, W)) ==> Mul(Clamp(X, Y, Z), W)" lhs rhs

rule02_v2 :: forall a. NumRule a
rule02_v2 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  tW <- newTensor @a "W" [rclass --> map]
  lhs <- clamp (numBinOp Sub tX tW) (numBinOp Sub tY tW) (numBinOp Sub tZ tW)
  rhs <- numBinOp Sub (clamp tX tY tZ) tW
  rewrite "Clamp(Sub(X, W), Sub(Y, W), Sub(Z, W)) ==> Sub(Clamp(X, Y, Z), W)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule02_v1 ##############################"
  verifyNumDSL rule02_v1
  print "############################## rule02_v2 ##############################"
  verifyNumDSL rule02_v2
