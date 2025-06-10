module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  c1 <- constant @a "c1" [rclass --> map]
  c2 <- constant @a "c2" [rclass --> map]
  lhs <- numBinOp Add (numBinOp Add tA c1) c2
  rhs <- numBinOp Add tA (numBinOp Add c1 c2)
  rewrite "Add(Add(A, c1), c2) ⇒ Add(A, Add(c1, c2))" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  zeroTensor <- constant @a 0 [rclass --> map]
  lhs <- numBinOp Add tA zeroTensor
  let rhs = tA
  rewrite "Add(A, 0) ⇒ A" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  zeroTensor <- constant @a 0 [rclass --> map]
  lhs <- numBinOp Add zeroTensor tA
  let rhs = tA
  rewrite "Add(0, A) ⇒ A" lhs rhs

rule04 :: forall a. NumRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  c <- constant @a "c" [rclass --> map]
  lhs <- numBinOp Add c tA
  rhs <- numBinOp Add tA c
  rewrite "Add(Const, A) ⇒ Add(A, Const)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
