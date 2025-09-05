module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcLength] <-
    newMaps ["rcSize", "rcStart", "rcLength"] rclass

  tA <- newTensor @a "A" [rclass --> rcSize]
  lhs <-
    dynamicSlice tA $
      DySlice
        { start = [rclass --> rcStart],
          sizes = [rclass --> rcLength]
        }

  rcStride <- newConstMap "rcStride" 1 rclass
  rcEffectiveStart <-
    combineMap
      "rcEffectiveStart"
      (\[s, size, length] -> symMin (size - length) $ symMax 0 s)
      [rcStart, rcSize, rcLength]
  rcEnd <- combineMap "rcEnd" sum [rcEffectiveStart, rcLength]
  rhs <-
    slice tA $
      Slice
        { start = [rclass --> rcEffectiveStart],
          end = [rclass --> rcEnd],
          strides = [rclass --> rcStride]
        }

  rewrite "DynamicSlice(A) ⇒ Slice(A)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcLength] <- newMaps ["rcSize", "rcStart", "rcLength"] rclass

  tA <- newTensor @a "A" [rclass --> rcSize]
  lhs <-
    dynamicSlice tA $
      DySlice
        { start = [rclass --> rcStart],
          sizes = [rclass --> rcLength]
        }
  precondition [rcLength, rcSize] $ \[l, s] -> l .== s

  let rhs = tA
  rewrite "DynamicSlice(A,...) ⇒ A // output shape is the same as input shape" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0Length] <-
    newMaps ["rc0Size", "rc0Start", "rc0Length"] rclass0
  [rc1Size, rc1Start, rc1Length] <-
    newMaps ["rc1Size", "rc1Start", "rc1Length"] rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size]
  lhs <-
    dynamicSlice (broadcast tA [rclass1 --> rc1Size]) $
      DySlice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          sizes = [rclass0 --> rc0Length, rclass1 --> rc1Length]
        }
  rhs <-
    broadcast
      ( dynamicSlice tA $
          DySlice
            { start = [rclass0 --> rc0Start],
              sizes = [rclass0 --> rc0Length]
            }
      )
      [rclass1 --> rc1Length]
  rewrite "DynamicSlice(Broadcast(A), ...) ⇒ Broadcast(DynamicSlice(A, ...))" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcLength] <-
    newMaps ["rcSize", "rcStart", "rcLength"] rclass
  tA <- newTensor @a "A" [rclass --> rcSize @@ "label1"]
  lhs <-
    relabel
      ( dynamicSlice tA $
          DySlice
            { start = [ByLabel "label1" --> rcStart],
              sizes = [ByLabel "label1" --> rcLength]
            }
      )
      [ByLabel "label1" --> ByLabel "label2"]
  rhs <-
    dynamicSlice (relabel tA [ByLabel "label1" --> ByLabel "label2"]) $
      DySlice
        { start = [ByLabel "label2" --> rcStart],
          sizes = [ByLabel "label2" --> rcLength]
        }
  rewrite "DynamicSlice(Transpose(A), ...) ⇒ Transpose(DynamicSlice(A, ...))" lhs rhs

rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStartInner, rcStartOuter, rcLengthInner, rcLengthOuter] <-
    newMaps ["rcSize", "rcStartInner", "rcStartOuter", "rcLengthInner", "rcLengthOuter"] rclass

  tA <- newTensor @a "A" [rclass --> rcSize]
  dySliceInner <-
    dynamicSlice tA $
      DySlice
        { start = [rclass --> rcStartInner],
          sizes = [rclass --> rcLengthInner]
        }
  lhs <-
    dynamicSlice dySliceInner $
      DySlice
        { start = [rclass --> rcStartOuter],
          sizes = [rclass --> rcLengthOuter]
        }

  rcInnerEffectiveStart <-
    combineMap
      "rcInnerEffectiveStart"
      (\[s, size, length] -> symMin (size - length) $ symMax 0 s)
      [rcStartInner, rcSize, rcLengthInner]
  rcOuterEffectiveStart <-
    combineMap
      "rcOuterEffectiveStart"
      (\[s, innerLength, outerLength] -> symMin (innerLength - outerLength) $ symMax 0 s)
      [rcStartOuter, rcLengthInner, rcLengthOuter]
  rcStartRhs <- combineMap "rcStartRhs" sum [rcInnerEffectiveStart, rcOuterEffectiveStart]
  rhs <-
    dynamicSlice tA $
      DySlice
        { start = [rclass --> rcStartRhs],
          sizes = [rclass --> rcLengthOuter]
        }

  rewrite "DynamicSlice(DynamicSlice(A,...),...) ⇒ DynamicSlice(A,...)" lhs rhs

rule06 :: DSLContext Rewrite
rule06 = do
  rclass <- newRClass "rclass"
  [sizeMap, startMap, lengthMap] <-
    newMaps ["sizeMap", "startMap", "lengthMap"] rclass

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

-- DynamicSlice clamps every start independently. If one output dimension has
-- the operand's full extent, its effective start is always zero.
-- https://github.com/openxla/xla/blob/cb214917224f5643aa8efc96823a920c42f47336/xla/hlo/transforms/simplifiers/algebraic_simplifier.cc#L7978-L7999
rule07 :: forall a. AnyDTypeRule a
rule07 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0Length] <-
    newMaps ["rc0Size", "rc0Start", "rc0Length"] rclass0
  [rc1Size, rc1Start, rc1Length] <-
    newMaps ["rc1Size", "rc1Start", "rc1Length"] rclass1
  rc0Zero <- newConstMap "rc0Zero" 0 rclass0

  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <-
    dynamicSlice tA $
      DySlice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          sizes = [rclass0 --> rc0Length, rclass1 --> rc1Length]
        }
  precondition [rc0Length, rc0Size] $ \[length, size] -> length .== size
  rhs <-
    dynamicSlice tA $
      DySlice
        { start = [rclass0 --> rc0Zero, rclass1 --> rc1Start],
          sizes = [rclass0 --> rc0Length, rclass1 --> rc1Length]
        }
  rewrite "DynamicSlice(A, full dimension, ...) ⇒ DynamicSlice(A, start=0, ...)" lhs rhs

main :: IO ()
main = do
  printTitle "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  printTitle "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
  printTitle "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  printTitle "############################## rule04 ##############################"
  verifyAnyDTypeDSL rule04
  printTitle "############################## rule05 ##############################"
  verifyAnyDTypeDSL rule05
  print "############################## rule07 ##############################"
  verifyAnyDTypeDSL rule07
