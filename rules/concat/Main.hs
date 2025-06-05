module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rclass0size <- newMap "rclass0size" rclass0
  [rclass1size0, rclass1size1] <- newMaps ["rclass1size0", "rclass1size1"] rclass1
  t1 <- newTensor @a "t1" [rclass0 --> rclass0size, rclass1 --> rclass1size0 @@ "label1"]
  t2 <- newTensor @a "t2" [rclass0 --> rclass0size, rclass1 --> rclass1size1 @@ "label1"]
  lhs <- concatTensorList [t1, t2] (ByLabel "label1")
  rhs <- concatTensor t1 t2 (ByLabel "label1")
  rewrite "ConcatList(A, B) ⇒ Concat(A, B)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rclass0size <- newMap "rclass0size" rclass0
  [rclass1size0, rclass1size1, rclass1size2] <- newMaps ["rclass1size0", "rclass1size1", "rclass1size2"] rclass1
  t1 <- newTensor @a "t1" [rclass0 --> rclass0size, rclass1 --> rclass1size0 @@ "label1"]
  t2 <- newTensor @a "t2" [rclass0 --> rclass0size, rclass1 --> rclass1size1 @@ "label1"]
  t3 <- newTensor @a "t3" [rclass0 --> rclass0size, rclass1 --> rclass1size2 @@ "label1"]
  lhs <- concatTensor t1 (concatTensor t2 t3 (ByLabel "label1")) (ByLabel "label1")
  rhs <- concatTensor (concatTensor t1 t2 (ByLabel "label1")) t3 (ByLabel "label1")
  rewrite "Concat(A, Concat(B, C)) ⇒ Concat(Concat(A, B), C)" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rclass0size <- newMap "rclass0size" rclass0
  [rclass1size0, rclass1size1, rclass1size2] <- newMaps ["rclass1size0", "rclass1size1", "rclass1size2"] rclass1
  t1 <- newTensor @a "t1" [rclass0 --> rclass0size, rclass1 --> rclass1size0 @@ "label1"]
  t2 <- newTensor @a "t2" [rclass0 --> rclass0size, rclass1 --> rclass1size1 @@ "label1"]
  t3 <- newTensor @a "t3" [rclass0 --> rclass0size, rclass1 --> rclass1size2 @@ "label1"]
  lhs <- concatTensorList [t1, t2, t3] (ByLabel "label1")
  rhs <- concatTensor t1 (concatTensor t2 t3 (ByLabel "label1")) (ByLabel "label1")
  rewrite "ConcatList(A, B, C) ⇒ Concat(A, Concat(B, C))" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rclass0sizeMap, rclass0endMap, rclass0startMap, rclass0strideMap] <- newMaps ["rclass0sizeMap", "rclass0endMap", "rclass0startMap", "rclass0strideMap"] rclass0
  [rclass1sizeMap, rclass1startMap1, rclass1endMap1, rclass1startMap2, rclass1endMap2, rclass1strideMap] <- newMaps ["rclass1sizeMap", "rclass1startMap1", "rclass1endMap1", "rclass1startMap2", "rclass1endMap2", "rclass1strideMap"] rclass1
  tensor <- newTensor @a "tensor" [rclass0 --> rclass0sizeMap, rclass1 --> rclass1sizeMap]
  lhs <- concatTensor (slice tensor [rclass0 --> rclass0startMap, rclass1 --> rclass1startMap1] [rclass0 --> rclass0endMap, rclass1 --> rclass1endMap1] [rclass0 --> rclass0strideMap, rclass1 --> rclass1strideMap]) (slice tensor [rclass0 --> rclass0startMap, rclass1 --> rclass1startMap2] [rclass0 --> rclass0endMap, rclass1 --> rclass1endMap2] [rclass0 --> rclass0strideMap, rclass1 --> rclass1strideMap]) (ByRClass rclass1)
  rhs <- slice tensor [rclass0 --> rclass0startMap, rclass1 --> rclass1startMap1] [rclass0 --> rclass0endMap, rclass1 --> rclass1endMap2] [rclass0 --> rclass0strideMap, rclass1 --> rclass1strideMap]
  precondition [rclass1strideMap] $ \[rclass1stride] -> rclass1stride .== 1
  precondition [rclass1endMap1, rclass1startMap2] $
    \[rclass1end1, rclass1start2] -> rclass1end1 .== rclass1start2
  rewrite "Concat(Slice(A), Slice(A)) ⇒ Slice(A)" lhs rhs

rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMap0, lowMap0, zeroMap0] <- newMaps ["sizeMap0", "lowMap0", "zeroMap0"] rclass0
  [sizeMap1, zeroMap1] <- newMaps ["sizeMap1", "zeroMap1"] rclass1
  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0, rclass1 --> sizeMap1]
  lhs <- concatTensor (constant @a "a" [rclass0 --> lowMap0, rclass1 --> sizeMap1]) tensor (ByRClass rclass0)
  rhs <- pad tensor ("a" :: a) [rclass0 --> lowMap0, rclass1 --> zeroMap1] [rclass0 --> zeroMap0, rclass1 --> zeroMap1] [rclass0 --> zeroMap0, rclass1 --> zeroMap1]
  precondition [lowMap0] $ \[low0] -> low0 .>= 0
  precondition [zeroMap0] $ \[zero0] -> zero0 .== 0
  precondition [zeroMap1] $ \[zero1] -> zero1 .== 0
  rewrite "Concat(Broadcast(Scalar), B) ⇒ Pad(B, scalar, low)" lhs rhs

rule06 :: forall a. AnyDTypeRule a
rule06 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMap0, highMap0, zeroMap0] <- newMaps ["sizeMap0", "highMap0", "zeroMap0"] rclass0
  [sizeMap1, zeroMap1] <- newMaps ["sizeMap1", "zeroMap1"] rclass1
  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0, rclass1 --> sizeMap1]
  lhs <- concatTensor tensor (constant @a "a" [rclass0 --> highMap0, rclass1 --> sizeMap1]) (ByRClass rclass0)
  rhs <- pad tensor ("a" :: a) [rclass0 --> zeroMap0, rclass1 --> zeroMap1] [rclass0 --> zeroMap0, rclass1 --> zeroMap1] [rclass0 --> highMap0, rclass1 --> zeroMap1]
  precondition [highMap0] $ \[high0] -> high0 .>= 0
  precondition [zeroMap0] $ \[zero0] -> zero0 .== 0
  precondition [zeroMap1] $ \[zero1] -> zero1 .== 0
  rewrite "Concat(A, Broadcast(Scalar)) ⇒ Pad(A, scalar, high)" lhs rhs

rule07 :: forall a. AnyDTypeRule a
rule07 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rclass0size <- newMap "rclass0size" rclass0
  [rclass1size0, rclass1size1, rclass1size2] <- newMaps ["rclass1size0", "rclass1size1", "rclass1size2"] rclass1
  t1 <- newTensor @a "t1" [rclass0 --> rclass0size, rclass1 --> rclass1size0 @@ "label1"]
  t2 <- newTensor @a "t2" [rclass0 --> rclass0size, rclass1 --> rclass1size1 @@ "label1"]
  t3 <- newTensor @a "t3" [rclass0 --> rclass0size, rclass1 --> rclass1size2 @@ "label1"]
  lhs <- concatTensor t1 (concatTensor t2 t3 (ByLabel "label1")) (ByLabel "label1")
  rhs <- concatTensorList [t1, t2, t3] (ByLabel "label1")
  rewrite "Concat(A, Concat(B, C)) ⇒ ConcatList(A, B, C)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  print "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
  print "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  print "############################## rule04 ##############################"
  verifyAnyDTypeDSL rule04
  print "############################## rule05 ##############################"
  verifyAnyDTypeDSL rule05
  print "############################## rule06 ##############################"
  verifyAnyDTypeDSL rule06
  print "############################## rule07 ##############################"
  verifyAnyDTypeDSL rule07
