module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass

  tA <- newTensor @a "A" [rclass --> map]
  lhs <- reverseTensor tA [ByRClass rclass]
  precondition [map] $ \[s] -> s .== 1

  let rhs = tA
  rewrite "Reverse(A, dims) ⇒ A" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <- reverseTensor (reverseTensor tA [ByRClass rclass0]) [ByRClass rclass0]
  let rhs = tA
  rewrite "Reverse(Reverse(A, dims1), dims2) ⇒ A" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  rc2Size <- newMap "rc2Size" rclass2
  tA <-
    newTensor @a
      "A"
      [ rclass0 --> rc0Size,
        rclass1 --> rc1Size,
        rclass2 --> rc2Size
      ]
  lhs <-
    reverseTensor
      (reverseTensor tA [ByRClass rclass0, ByRClass rclass1])
      [ByRClass rclass1, ByRClass rclass2]
  rhs <- reverseTensor tA [ByRClass rclass2, ByRClass rclass0]
  rewrite
    "Reverse(Reverse(A, dims1), dims2) ⇒ Reverse(A, disjoint union of dims1 and dims2)"
    lhs
    rhs

rule04 :: forall a. NumRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  const <- constant @a "const" [rclass --> map]
  lhs <- reverseTensor (numBinOp Add tA const) [ByRClass rclass]
  rhs <- numBinOp Add (reverseTensor tA [ByRClass rclass]) const
  rewrite
    "Reverse(Binary(A, Const)) ⇒ Binary(Reverse(A), Const)"
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
