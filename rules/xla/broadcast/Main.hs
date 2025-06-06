module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  map0 <- newMap "map0" rclass0
  map1 <- newMap "map1" rclass1
  tensor0 <- newTensor @a "tensor0" [rclass0 --> map0]
  tensor1 <- newTensor @a "tensor1" [rclass0 --> map0]
  lhs <- numBinOp Add (broadcast tensor0 [rclass1 --> map1]) (broadcast tensor1 [rclass1 --> map1])
  rhs <- broadcast (numBinOp Add tensor0 tensor1) [rclass1 --> map1]
  rewrite "Add(Broadcast(A),Broadcast(B)) ⇒ Broadcast(Add(A,B))" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  map0 <- newMap "map0" rclass0
  map1 <- newMap "map1" rclass1
  tensor0 <- newTensor @a "tensor0" [rclass0 --> map0]
  tensor1 <- newTensor @a "tensor1" [rclass0 --> map0]
  lhs <- numBinOp Mul (broadcast tensor0 [rclass1 --> map1]) (broadcast tensor1 [rclass1 --> map1])
  rhs <- broadcast (numBinOp Mul tensor0 tensor1) [rclass1 --> map1]
  rewrite "Mul(Broadcast(A),Broadcast(B)) ⇒ Broadcast(Mul(A,B))" lhs rhs

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
  [origSizeMap, newSizeMap, startMap, endMap, strideMap] <- newMaps ["origSizeMap", "newSizeMap", "startMap", "endMap", "strideMap"] rclass
  lhs <- slice (constant @a "a" [rclass --> origSizeMap]) [rclass --> startMap] [rclass --> endMap] [rclass --> strideMap]
  rhs <- constant @a "a" [rclass --> newSizeMap]
  precondition [newSizeMap, startMap, endMap, strideMap] $
    \[newSize, start, end, stride] -> end .== start + newSize * stride
  rewrite "Slice(Broadcast(Scalar)) ⇒ Broadcast(Scalar)" lhs rhs

rule06 :: forall a. AnyDTypeRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  [origSizeMap, newSizeMap, startMap] <- newMaps ["origSizeMap", "newSizeMap", "startMap"] rclass
  lhs <- dynamicSlice (constant @a "a" [rclass --> origSizeMap]) DySlice {start = [rclass --> startMap], sizes = [rclass --> newSizeMap]}
  rhs <- constant @a "a" [rclass --> newSizeMap]
  rewrite "DynamicSlice(Broadcast(Scalar)) ⇒ Broadcast(Scalar)" lhs rhs

rule07 :: DSLContext Rewrite
rule07 = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  map0 <- newMap "map0" rclass0
  map1 <- newMap "map1" rclass1
  lhs <- broadcast (iota [rclass0 --> map0] (ByRClass rclass0)) [rclass1 --> map1]
  rhs <- iota [rclass0 --> map0, rclass1 --> map1] (ByRClass rclass0)
  rewrite "Broadcast(Iota) ⇒ Iota" lhs rhs

rule08 :: forall a. AnyDTypeRule a
rule08 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  map0 <- newMap "map0" rclass0
  map1 <- newMap "map1" rclass1
  map2 <- newMap "map2" rclass2
  tensor <- newTensor @a "tensor" [rclass0 --> map0]
  lhs <- broadcast (broadcast tensor [rclass1 --> map1]) [rclass2 --> map2]
  rhs <- broadcast tensor [rclass1 --> map1, rclass2 --> map2]
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
