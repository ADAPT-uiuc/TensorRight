module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  t <- newTensor @a "t" [rclass --> map]
  lhs <- reverseTensor t [ByRClass rclass]
  let rhs = t
  precondition [map] $ \[map'] -> map' .== 1
  rewrite
    "Reverse(A,dims) ⇒ A"
    lhs
    rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  map0 <- newMap "map0" rclass0
  map1 <- newMap "map1" rclass1
  t <- newTensor @a "t" [rclass0 --> map0, rclass1 --> map1]
  lhs <- reverseTensor (reverseTensor t [ByRClass rclass0]) [ByRClass rclass0]
  let rhs = t
  rewrite "Reverse(Reverse(A,dims1),dims2) ⇒ A" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  map0 <- newMap "map0" rclass0
  map1 <- newMap "map1" rclass1
  map2 <- newMap "map2" rclass2
  t <- newTensor @a "t" [rclass0 --> map0, rclass1 --> map1, rclass2 --> map2]
  lhs <-
    reverseTensor
      (reverseTensor t [ByRClass rclass0, ByRClass rclass1])
      [ByRClass rclass1, ByRClass rclass2]
  rhs <- reverseTensor t [ByRClass rclass2, ByRClass rclass0]
  rewrite
    "Reverse(Reverse(A,dims1),dims2) ⇒ Reverse(A, disjoint union of dims1 and dims2)"
    lhs
    rhs

rule04 :: forall a. NumRule a
rule04 _ = do
  [rclass0] <- newRClasses ["rclass0"]
  map0 <- newMap "map0" rclass0
  t <- newTensor @a "t" [rclass0 --> map0]
  const <- constant @a "const" [rclass0 --> map0]
  lhs <- reverseTensor (numBinOp Add t const) [ByRClass rclass0]
  rhs <- numBinOp Add (reverseTensor t [ByRClass rclass0]) const
  rewrite
    "Reverse(Binary(A,Const)) ⇒ Binary(Reverse(A),Const)"
    lhs
    rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  print "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
  print "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
