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
  rcEnd <- combineMap "rcEnd" sum [rcStart, rcLength]
  rhs <-
    slice tA $
      Slice
        { start = [rclass --> rcStart],
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
  precondition [rcStart] $ \[s] -> s .== 0
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

  rcStartRhs <- combineMap "rcStartRhs" sum [rcStartInner, rcStartOuter]
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
