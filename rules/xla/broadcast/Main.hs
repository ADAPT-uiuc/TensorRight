module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size]
  tB <- newTensor @a "B" [rclass0 --> rc0Size]
  lhs <- numBinOp Add (broadcast tA [rclass1 --> rc1Size]) (broadcast tB [rclass1 --> rc1Size])
  rhs <- broadcast (numBinOp Add tA tB) [rclass1 --> rc1Size]
  rewrite "Add(Broadcast(A), Broadcast(B)) ⇒ Broadcast(Add(A, B))" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size]
  tB <- newTensor @a "B" [rclass0 --> rc0Size]
  lhs <- numBinOp Mul (broadcast tA [rclass1 --> rc1Size]) (broadcast tB [rclass1 --> rc1Size])
  rhs <- broadcast (numBinOp Mul tA tB) [rclass1 --> rc1Size]
  rewrite "Mul(Broadcast(A), Broadcast(B)) ⇒ Broadcast(Mul(A, B))" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  lhsTensor <- constant @a "a" [rclass --> map @@ "label1"]
  rhsTensor <- constant @a "a" [rclass --> map @@ "label2"]
  lhs <- relabel lhsTensor [ByLabel "label1" --> ByLabel "label2"]
  let rhs = rhsTensor
  rewrite "Transpose(Broadcast(Scalar)) ⇒ Broadcast(Scalar)" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  lhs <- reverseTensor (constant @a "a" [rclass --> map]) [ByRClass rclass]
  rhs <- constant @a "a" [rclass --> map]
  rewrite "Reverse(Broadcast(Scalar)) ⇒ Broadcast(Scalar)" lhs rhs

rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  [origSize, start, end, stride] <-
    newMaps ["origSize", "start", "end", "stride"] rclass

  lhs <-
    slice (constant @a "a" [rclass --> origSize]) $
      Slice
        { start = [rclass --> start],
          end = [rclass --> end],
          strides = [rclass --> stride]
        }

  newSize <-
    combineMap
      "newSize"
      (\[s, e, p] -> divOr 0 (e - s + p - 1) p)
      [start, end, stride]
  rhs <- constant @a "a" [rclass --> newSize]
  rewrite "Slice(Broadcast(Scalar)) ⇒ Broadcast(Scalar)" lhs rhs

rule06 :: forall a. AnyDTypeRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  [origSize, newSize, start] <- newMaps ["origSize", "newSize", "start"] rclass
  lhs <-
    dynamicSlice (constant @a "a" [rclass --> origSize]) $
      DySlice
        { start = [rclass --> start],
          sizes = [rclass --> newSize]
        }
  rhs <- constant @a "a" [rclass --> newSize]
  rewrite "DynamicSlice(Broadcast(Scalar)) ⇒ Broadcast(Scalar)" lhs rhs

rule07 :: DSLContext Rewrite
rule07 = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  lhs <-
    broadcast
      (iota [rclass0 --> rc0Size] (ByRClass rclass0))
      [rclass1 --> rc1Size]
  rhs <- iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)
  rewrite "Broadcast(Iota) ⇒ Iota" lhs rhs

rule08 :: forall a. AnyDTypeRule a
rule08 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  rc2Size <- newMap "rc2Size" rclass2
  tA <- newTensor @a "A" [rclass0 --> rc0Size]
  lhs <- broadcast (broadcast tA [rclass1 --> rc1Size]) [rclass2 --> rc2Size]
  rhs <- broadcast tA [rclass1 --> rc1Size, rclass2 --> rc2Size]
  rewrite "Broadcast(Broadcast(A, shape, dims), shape2, dims2) ⇒ Broadcast(A, shape3, dims3)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  print "############################## rule04 ##############################"
  verifyAnyDTypeDSL rule04
  print "############################## rule05 ##############################"
  verifyAnyDTypeDSL rule05
  print "############################## rule06 ##############################"
  verifyAnyDTypeDSL rule06
  print "############################## rule07 ##############################"
  verifyDSL rule07
  print "############################## rule08 ##############################"
  verifyAnyDTypeDSL rule08
