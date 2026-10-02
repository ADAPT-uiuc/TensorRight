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
  rcEffectiveStart <-
    combineMap
      "rcEffectiveStart"
      (\[s, newSize, origSize] -> symMin (newSize - origSize) $ symMax 0 s)
      [rcStart, rcNewSize, rcOrigSize]
  rcHigh <- combineMap "rcHigh" (\[ns, os, s] -> ns - os - s) [rcNewSize, rcOrigSize, rcEffectiveStart]
  rhs <-
    pad tA ("a" :: a) $
      Padding
        { low = [rclass --> rcEffectiveStart],
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

  let rhs = tB
  rewrite "DynamicUpdateSlice(A, B, ...) ⇒ B // update shape is the same as input shape" lhs rhs

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

  rcOuterEffectiveStart <-
    combineMap
      "rcOuterEffectiveStart"
      (\[s, origSize, innerSize] -> symMin (origSize - innerSize) $ symMax 0 s)
      [rcStart0, rcSizeA, rcLength]
  rcInnerEffectiveStart <-
    combineMap
      "rcInnerEffectiveStart"
      (\[s, innerSize, updateSize] -> symMin (innerSize - updateSize) $ symMax 0 s)
      [rcStart1, rcLength, rcSizeB]
  rcStart2 <- combineMap "rcStart2" sum [rcOuterEffectiveStart, rcInnerEffectiveStart]
  rhs <- dynamicUpdateSlice tA tB [rclass --> rcStart2]
  rewrite "DynamicUpdateSlice(A, DynamicUpdateSlice(DynamicSlice(A, ...), B, ...), ...)) ⇒ DynamicUpdateSlice(A, B, ...)" lhs rhs

-- DynamicUpdateSlice clamps every start independently. If one update dimension
-- has the operand's full extent, its effective start is always zero.
-- https://github.com/openxla/xla/blob/cb214917224f5643aa8efc96823a920c42f47336/xla/hlo/transforms/simplifiers/algebraic_simplifier.cc#L8440-L8463
rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeA, rc0SizeB, rc0Start] <-
    newMaps ["rc0SizeA", "rc0SizeB", "rc0Start"] rclass0
  [rc1SizeA, rc1SizeB, rc1Start] <-
    newMaps ["rc1SizeA", "rc1SizeB", "rc1Start"] rclass1
  rc0Zero <- newConstMap "rc0Zero" 0 rclass0

  tA <- newTensor @a "A" [rclass0 --> rc0SizeA, rclass1 --> rc1SizeA]
  tB <- newTensor @a "B" [rclass0 --> rc0SizeB, rclass1 --> rc1SizeB]
  lhs <- dynamicUpdateSlice tA tB [rclass0 --> rc0Start, rclass1 --> rc1Start]
  precondition [rc0SizeA, rc0SizeB] $ \[sizeA, sizeB] -> sizeA .== sizeB
  rhs <- dynamicUpdateSlice tA tB [rclass0 --> rc0Zero, rclass1 --> rc1Start]
  rewrite "DynamicUpdateSlice(A, B, full update dimension, ...) ⇒ DynamicUpdateSlice(A, B, start=0, ...)" lhs rhs

-- Slice(DynamicUpdateSlice(base, update, start), effective-start, update-size)
-- is update. XLA compares the Slice bounds with the clamped start.
-- https://github.com/openxla/xla/blob/cb214917224f5643aa8efc96823a920c42f47336/xla/hlo/transforms/simplifiers/algebraic_simplifier.cc#L7541-L7600
rule06 :: forall a. AnyDTypeRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  [rcSizeA, rcSizeB, rcStart] <- newMaps ["rcSizeA", "rcSizeB", "rcStart"] rclass
  rcStride <- newConstMap "rcStride" 1 rclass
  rcEffectiveStart <-
    combineMap
      "rcEffectiveStart"
      (\[start, sizeA, sizeB] -> symMin (sizeA - sizeB) $ symMax 0 start)
      [rcStart, rcSizeA, rcSizeB]
  rcEnd <- combineMap "rcEnd" sum [rcEffectiveStart, rcSizeB]

  tA <- newTensor @a "A" [rclass --> rcSizeA]
  tB <- newTensor @a "B" [rclass --> rcSizeB]
  lhs <-
    slice (dynamicUpdateSlice tA tB [rclass --> rcStart]) $
      Slice
        { start = [rclass --> rcEffectiveStart],
          end = [rclass --> rcEnd],
          strides = [rclass --> rcStride]
        }
  rewrite "Slice(DynamicUpdateSlice(A, B, ...), effective start, update size) ⇒ B" lhs tB

-- DynamicUpdateSlice(Pad(A, high=B), B, start=A) ⇒ Concat(A, B).
-- https://github.com/openxla/xla/blob/cb214917224f5643aa8efc96823a920c42f47336/xla/hlo/transforms/simplifiers/algebraic_simplifier.cc#L8348-L8435
rule07 :: forall a. AnyDTypeRule a
rule07 _ = do
  rclass <- newRClass "rclass"
  [rcSizeA, rcSizeB] <- newMaps ["rcSizeA", "rcSizeB"] rclass
  rcZero <- newConstMap "rcZero" 0 rclass
  tA <- newTensor @a "A" [rclass --> rcSizeA]
  tB <- newTensor @a "B" [rclass --> rcSizeB]
  lhs <-
    dynamicUpdateSlice
      (pad tA ("a" :: a) $ Padding {low = [rclass --> rcZero], high = [rclass --> rcSizeB], interior = [rclass --> rcZero]})
      tB
      [rclass --> rcSizeA]
  rhs <- concatTensor tA tB $ ByRClass rclass
  rewrite "DynamicUpdateSlice(Pad(A, high=B), B, A) ⇒ Concat(A, B)" lhs rhs

-- DynamicUpdateSlice(Pad(A, low=B), B, start=0) ⇒ Concat(B, A).
-- https://github.com/openxla/xla/blob/cb214917224f5643aa8efc96823a920c42f47336/xla/hlo/transforms/simplifiers/algebraic_simplifier.cc#L8348-L8435
rule08 :: forall a. AnyDTypeRule a
rule08 _ = do
  rclass <- newRClass "rclass"
  [rcSizeA, rcSizeB] <- newMaps ["rcSizeA", "rcSizeB"] rclass
  rcZero <- newConstMap "rcZero" 0 rclass
  tA <- newTensor @a "A" [rclass --> rcSizeA]
  tB <- newTensor @a "B" [rclass --> rcSizeB]
  lhs <-
    dynamicUpdateSlice
      (pad tA ("a" :: a) $ Padding {low = [rclass --> rcSizeB], high = [rclass --> rcZero], interior = [rclass --> rcZero]})
      tB
      [rclass --> rcZero]
  rhs <- concatTensor tB tA $ ByRClass rclass
  rewrite "DynamicUpdateSlice(Pad(A, low=B), B, 0) ⇒ Concat(B, A)" lhs rhs

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
  print "############################## rule05 ##############################"
  verifyAnyDTypeDSL rule05
  print "############################## rule06 ##############################"
  verifyAnyDTypeDSL rule06
  print "############################## rule07 ##############################"
  verifyAnyDTypeDSL rule07
  print "############################## rule08 ##############################"
  verifyAnyDTypeDSL rule08
