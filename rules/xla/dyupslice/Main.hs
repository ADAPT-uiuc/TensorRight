module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [rcSizeA, rcSizeB, rcStart] <-
    newMaps ["rcSizeA", "rcSizeB", "rcStart"] rclass
  tA <- newTensor @a "A" [rclass --> rcSizeA]
  tB <- newTensor @a "B" [rclass --> rcSizeB]
  lhs <-
    numBinOp
      Add
      tA
      (dynamicUpdateSlice (constant @a 0 [rclass --> rcSizeA]) tB [rclass --> rcStart])
  rhs <-
    dynamicUpdateSlice
      tA
      ( numBinOp
          Add
          tB
          ( dynamicSlice tA $
              DySlice
                { start = [rclass --> rcStart],
                  sizes = [rclass --> rcSizeB]
                }
          )
      )
      [rclass --> rcStart]
  rewrite "Add(A, DynamicUpdateSlice(Broadcast(0), B) ⇒ DynamicUpdateSlice(A,...)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  [rcOrigSize, rcNewSize, rcStart] <-
    newMaps ["rcOrigSize", "rcNewSize", "rcStart"] rclass

  tA <- newTensor @a "A" [rclass --> rcOrigSize]
  lhs <-
    dynamicUpdateSlice
      (constant @a "a" [rclass --> rcNewSize])
      tA
      [rclass --> rcStart]

  rcInt <- newConstMap "rcInt" 0 rclass
  rcHigh <- combineMap "rcHigh" (\[ns, os, s] -> ns - os - s) [rcNewSize, rcOrigSize, rcStart]
  rhs <-
    pad tA ("a" :: a) $
      Padding
        { low = [rclass --> rcStart],
          high = [rclass --> rcHigh],
          interior = [rclass --> rcInt]
        }

  rewrite "DynamicUpdateSlice(Broadcast(Const),A,...) ⇒ Pad(" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart] <- newMaps ["rcSize", "rcStart"] rclass

  tA <- newTensor @a "tA" [rclass --> rcSize]
  tB <- newTensor @a "tB" [rclass --> rcSize]
  lhs <- dynamicUpdateSlice tA tB [rclass --> rcStart]
  precondition [rcSize] $ \[s] -> s .== 0

  let rhs = tB
  rewrite "DynamicUpdateSlice(A, B, 0) ⇒ B" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  [rcSizeA, rcSizeB, rcStart0, rcLength, rcStart1] <-
    newMaps ["rcSizeA", "rcSizeB", "startMap0", "sliceSizeMap0", "startMap1"] rclass

  tA <- newTensor @a "A" [rclass --> rcSizeA]
  tB <- newTensor @a "B" [rclass --> rcSizeB]
  lhs <-
    dynamicUpdateSlice
      tA
      ( dynamicUpdateSlice
          ( dynamicSlice tA $
              DySlice
                { start = [rclass --> rcStart0],
                  sizes = [rclass --> rcLength]
                }
          )
          tB
          [rclass --> rcStart1]
      )
      [rclass --> rcStart0]

  rcStart2 <- combineMap "rcStart2" sum [rcStart0, rcStart1]
  rhs <- dynamicUpdateSlice tA tB [rclass --> rcStart2]
  rewrite "DynamicUpdateSlice(A, DynamicUpdateSlice(DynamicSlice(A, ...), B, ...), ...)) ⇒ DynamicUpdateSlice(A, B, ...)" lhs rhs

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
