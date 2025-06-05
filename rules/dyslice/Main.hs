module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [rclassSize, rclassStart, rclassLength, rclassEnd, rclassStride] <-
    newMaps ["rclassSize", "rclassStart", "rclassLength", "rclassEnd", "rclassStride"] rclass

  tensor <- newTensor @a "tensor" [rclass --> rclassSize]

  lhs <-
    dynamicSlice tensor $
      DySlice {start = [rclass --> rclassStart], sizes = [rclass --> rclassLength]}
  rhs <-
    slice tensor $
      Slice
        { start = [rclass --> rclassStart],
          end = [rclass --> rclassEnd],
          strides = [rclass --> rclassStride]
        }

  precondition [rclassStride] $ \[rclassStride] -> rclassStride .== 1
  precondition [rclassEnd, rclassStart, rclassLength] $
    \[rclassEnd, rclassStart, rclassLength] -> rclassEnd .== rclassStart + rclassLength

  rewrite "DynamicSlice(A) ⇒ Slice(A)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, startMap, sliceSizeMap] <- newMaps ["sizeMap", "startMap", "sliceSizeMap"] rclass
  tensor <- newTensor @a "tensor" [rclass --> sizeMap]
  lhs <- dynamicSlice tensor DySlice {start = [rclass --> startMap], sizes = [rclass --> sliceSizeMap]}
  let rhs = tensor
  precondition [startMap] $ \[start] -> start .== 0
  precondition [sliceSizeMap, sizeMap] $ \[sliceSize, size] -> sliceSize .== size
  rewrite "DynamicSlice(A,...) ⇒ A // output shape is the same as input shape" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMap0, startMap0, sliceSizeMap0] <- newMaps ["sizeMap0", "startMap0", "sliceSizeMap0"] rclass0
  [sizeMap1, startMap1, sliceSizeMap1] <- newMaps ["sizeMap1", "startMap1", "sliceSizeMap1"] rclass1
  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0]
  lhs <- dynamicSlice (broadcast tensor [rclass1 --> sizeMap1]) DySlice {start = [rclass0 --> startMap0, rclass1 --> startMap1], sizes = [rclass0 --> sliceSizeMap0, rclass1 --> sliceSizeMap1]}
  rhs <- broadcast (dynamicSlice tensor DySlice {start = [rclass0 --> startMap0], sizes = [rclass0 --> sliceSizeMap0]}) [rclass1 --> sliceSizeMap1]
  rewrite "DynamicSlice(Broadcast(A),...) ⇒ Broadcast(DynamicSlice(A,...))" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, startMap, sliceSizeMap] <- newMaps ["sizeMap", "startMap", "sliceSizeMap"] rclass
  tensor <- newTensor @a "tensor" [rclass --> sizeMap @@ "label1"]
  lhs <- relabel (dynamicSlice tensor DySlice {start = [ByLabel "label1" --> startMap], sizes = [ByLabel "label1" --> sliceSizeMap]}) [ByLabel "label1" --> ByLabel "label2"]
  rhs <- dynamicSlice (relabel tensor [ByLabel "label1" --> ByLabel "label2"]) DySlice {start = [ByLabel "label2" --> startMap], sizes = [ByLabel "label2" --> sliceSizeMap]}
  rewrite "DynamicSlice(Transpose(A),...) ⇒ Transpose(DynamicSlice(A,...))" lhs rhs

rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, startMap1, startMap2, startMap3, sliceSizeMap1, sliceSizeMap2, sliceSizeMap3] <- newMaps ["sizeMap", "startMap1", "startMap2", "startMap3", "sliceSizeMap1", "sliceSizeMap2", "sliceSizeMap3"] rclass
  tensor <- newTensor @a "tensor" [rclass --> sizeMap]
  lhs <- dynamicSlice (dynamicSlice tensor DySlice {start = [rclass --> startMap1], sizes = [rclass --> sliceSizeMap1]}) DySlice {start = [rclass --> startMap2], sizes = [rclass --> sliceSizeMap2]}
  rhs <- dynamicSlice tensor DySlice {start = [rclass --> startMap3], sizes = [rclass --> sliceSizeMap3]}
  precondition [startMap1, startMap2, startMap3] $
    \[start1, start2, start3] -> start3 .== start1 + start2
  precondition [sliceSizeMap2, sliceSizeMap3] $
    \[sliceSize2, sliceSize3] -> sliceSize3 .== sliceSize2
  rewrite "DynamicSlice(DynamicSlice(A,...),...) ⇒ DynamicSlice(A,...)" lhs rhs

rule06 :: DSLContext Rewrite
rule06 = do
  rclass <- newRClass "rclass"
  [sizeMap, startMap, lengthMap] <- newMaps ["sizeMap", "startMap", "lengthMap"] rclass

  lhs <-
    dynamicSlice (iota [rclass --> sizeMap] (ByRClass rclass)) $
      DySlice
        { start = [rclass --> startMap],
          sizes = [rclass --> lengthMap]
        }
  rhsSize <- newConstMap "size" 1 rclass
  -- Cannot express rule since we need a precondition on "a"
  rhs <- constant @TensorInt "a" [rclass --> rhsSize]
  rewrite "DynamicSlice(Iota) ⇒ index" lhs rhs

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
