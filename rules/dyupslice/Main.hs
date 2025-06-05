module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [sizeMap0, sizeMap1, startMap0] <- newMaps ["sizeMap0", "sizeMap1", "startMap0"] rclass
  t1 <- newTensor @a "t1" [rclass --> sizeMap0]
  t2 <- newTensor @a "t2" [rclass --> sizeMap1]
  lhs <- numBinOp Add t1 (dynamicUpdateSlice (constant @a 0 [rclass --> sizeMap0]) t2 [rclass --> startMap0])
  rhs <- dynamicUpdateSlice t1 (numBinOp Add t2 (dynamicSlice t1 DySlice {start = [rclass --> startMap0], sizes = [rclass --> sizeMap1]})) [rclass --> startMap0]
  rewrite "Add(A, DynamicUpdateSlice(Broadcast(0), B) ⇒ DynamicUpdateSlice(A,...)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  [origSizeMap, newSizeMap, startMap, lowMap, interiorMap, highMap] <- newMaps ["origSizeMap", "newSizeMap", "startMap", "lowMap", "interiorMap", "highMap"] rclass
  tensor <- newTensor @a "tensor" [rclass --> origSizeMap]
  lhs <- dynamicUpdateSlice (constant @a "a" [rclass --> newSizeMap]) tensor [rclass --> startMap]
  rhs <- pad tensor ("a" :: a) [rclass --> lowMap] [rclass --> interiorMap] [rclass --> highMap]
  precondition [lowMap, startMap] $ \[low, start] -> low .== start
  precondition [interiorMap] $ \[interior] -> interior .== 0
  precondition [lowMap, highMap, origSizeMap, newSizeMap] $
    \[low, high, origSize, newSize] -> newSize .== origSize + low + high
  rewrite "DynamicUpdateSlice(Broadcast(Const),A,...) ⇒ Pad(" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, startMap] <- newMaps ["sizeMap", "startMap"] rclass
  t1 <- newTensor @a "t1" [rclass --> sizeMap]
  t2 <- newTensor @a "t2" [rclass --> sizeMap]
  lhs <- dynamicUpdateSlice t1 t2 [rclass --> startMap]
  let rhs = t2
  precondition [startMap] $ \[start] -> start .== 0
  rewrite "DynamicUpdateSlice(A, B, 0) ⇒ B" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  [sizeMap0, sizeMap1, startMap0, sliceSizeMap0, startMap1, startMap2] <- newMaps ["sizeMap0", "sizeMap1", "startMap0", "sliceSizeMap0", "startMap1", "startMap2"] rclass
  t1 <- newTensor @a "t1" [rclass --> sizeMap0]
  t2 <- newTensor @a "t2" [rclass --> sizeMap1]
  lhs <- dynamicUpdateSlice t1 (dynamicUpdateSlice (dynamicSlice t1 DySlice {start = [rclass --> startMap0], sizes = [rclass --> sliceSizeMap0]}) t2 [rclass --> startMap1]) [rclass --> startMap0]
  rhs <- dynamicUpdateSlice t1 t2 [rclass --> startMap2]
  precondition [startMap0, startMap1, startMap2] $
    \[start0, start1, start2] -> start2 .== start0 + start1
  rewrite "DynamicUpdateSlice(A, DynamicUpdateSlice(DynamicSlice(A,...), C ,...),...)) ⇒ DynamicUpdateSlice(A,C,...)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
  print "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  print "############################## rule04 ##############################"
  verifyAnyDTypeDSL rule04
