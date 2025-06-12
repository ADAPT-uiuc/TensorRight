module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcEnd, rcStride] <-
    newMaps ["rcSize", "rcStart", "rcEnd", "rcStride"] rclass

  tA <- newTensor @a "A" [rclass --> rcSize]
  lhs <-
    slice tA $
      Slice
        { start = [rclass --> rcStart],
          end = [rclass --> rcEnd],
          strides = [rclass --> rcStride]
        }
  precondition [rcStart] $ \[start] -> start .== 0
  precondition [rcSize, rcEnd] $ \[size, end] -> end .== size
  precondition [rcStride] $ \[stride] -> stride .== 1

  let rhs = tA
  rewrite "Slice(A) ⇒ A" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcEnd, rcStride] <-
    newMaps ["rcSize", "rcStart", "rcEnd", "rcStride"] rclass

  lhs <-
    slice (constant @a "a" [rclass --> rcSize]) $
      Slice
        { start = [rclass --> rcStart],
          end = [rclass --> rcEnd],
          strides = [rclass --> rcStride]
        }

  rcNewSize <- combineMap "rcNewSize" (\[s, e, p] -> divOr 0 (e - s + p - 1) p) [rcStart, rcEnd, rcStride]
  rhs <- constant @a "a" [rclass --> rcNewSize]
  rewrite "Slice(Const) ⇒ Const" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0End, rc0Stride] <-
    newMaps ["rc0Size", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1Start, rc1End, rc1Stride] <-
    newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Stride"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0Size]
  lhs <-
    slice (broadcast tA [rclass1 --> rc1Size]) $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          end = [rclass0 --> rc0End, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }

  rc1NewSize <- combineMap "rc1NewSize" (\[s, e, p] -> divOr 0 (e - s + p - 1) p) [rc1Start, rc1End, rc1Stride]
  rhs <-
    broadcast
      ( slice tA $
          Slice
            { start = [rclass0 --> rc0Start],
              end = [rclass0 --> rc0End],
              strides = [rclass0 --> rc0Stride]
            }
      )
      [rclass1 --> rc1NewSize]

  rewrite "Slice(Broadcast(A)) ⇒ Broadcast(Slice(A))" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  [rcStart, rcEnd, rcStride] <-
    newMaps ["rcStart", "rcEnd", "rcStride"] rclass
  -- TODO: Making `rcSize` a map instead of a non-negative map leads to a
  -- TIMEOUT
  [rcSize, rcLow, rcHigh, rcInt] <-
    newNonNegMaps ["rcSize", "rcLow", "rcHigh", "rcInt"] rclass
  tA <- newTensor @a "A" [rclass --> rcSize]

  lhs <-
    slice
      ( pad tA ("a" :: a) $
          Padding
            { low = [rclass --> rcLow],
              interior = [rclass --> rcInt],
              high = [rclass --> rcHigh]
            }
      )
      $ Slice
        { start = [rclass --> rcStart],
          end = [rclass --> rcEnd],
          strides = [rclass --> rcStride]
        }
  precondition [rcStart, rcLow] $ \[s, l] -> s .== l
  precondition [rcStride, rcInt] $ \[p, i] -> p .== i + 1
  precondition [rcSize, rcLow, rcInt, rcEnd] $
    \[sz, l, i, e] -> e .== sz + l + (sz - 1) * i
  -- TODO: The following precondition is not required since it is already
  -- implied by `highMap` being non-negative. However, removing it leads to
  -- a TIMEOUT
  precondition [rcHigh] $ \[h] -> h .>= 0

  let rhs = tA
  rewrite "Slice(Pad(A)) ⇒ A" lhs rhs

rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcEnd, rcStride, rcLow, rcHigh] <-
    newMaps ["rcSize", "rcEnd", "rcStride", "rcLow", "rcHigh"] rclass
  [startMap, intMap] <- newNonNegMaps ["startMap", "intMap"] rclass
  tA <- newTensor @a "A" [rclass --> rcSize]

  lhs <-
    slice
      ( pad tA ("a" :: a) $
          Padding
            { low = [rclass --> rcLow],
              interior = [rclass --> intMap],
              high = [rclass --> rcHigh]
            }
      )
      $ Slice
        { start = [rclass --> startMap],
          end = [rclass --> rcEnd],
          strides = [rclass --> rcStride]
        }
  precondition [rcSize, startMap, rcEnd, rcLow, intMap] $
    \[sz, s, e, l, i] -> e .<= l .|| s .>= sz + l + (sz - 1) * i

  rcNewSize <- combineMap "rcNewSize" (\[s, e, p] -> divOr 0 (e - s + p - 1) p) [startMap, rcEnd, rcStride]
  rhs <- constant @a "a" [rclass --> rcNewSize]

  rewrite "Slice(Pad(A, v)) ⇒ Broadcast(v)" lhs rhs

rule06 :: forall a. AnyDTypeRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  rcSize <- newMap "rcSize" rclass
  [rcStart, rcEnd, rcLow, rcHigh] <-
    newNonNegMaps ["rcStart", "rcEnd", "rcLow", "rcHigh"] rclass
  rcStride <- newConstMap "rcStride" 1 rclass
  rcInt <- newConstMap "rcInt" 0 rclass
  tA <- newTensor @a "A" [rclass --> rcSize]

  lhs <-
    slice
      ( pad tA ("a" :: a) $
          Padding
            { low = [rclass --> rcLow],
              interior = [rclass --> rcInt],
              high = [rclass --> rcHigh]
            }
      )
      $ Slice
        { start = [rclass --> rcStart],
          end = [rclass --> rcEnd],
          strides = [rclass --> rcStride]
        }
  precondition [rcStart, rcLow] $ \[s, l] -> s .>= l
  precondition [rcSize, rcEnd, rcLow, rcInt] $
    \[s, e, l, i] -> e .<= s + l + (s - 1) * i

  rcNewStart <- combineMap "rcNewStart" (\[a, b] -> a - b) [rcStart, rcLow]
  rcNewEnd <- combineMap "rcNewEnd" (\[a, b] -> a - b) [rcEnd, rcLow]
  rhs <-
    slice tA $
      Slice
        { start = [rclass --> rcNewStart],
          end = [rclass --> rcNewEnd],
          strides = [rclass --> rcStride]
        }
  rewrite "Slice(Pad(A, v)) ⇒ Slice(A)" lhs rhs

rule07 :: forall a. AnyDTypeRule a
rule07 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcOuterEnd, rcInnerEnd] <-
    newMaps ["rcSize", "rcOuterEnd", "rcInnerEnd"] rclass
  [rcOuterStart, rcInnerStart] <-
    newMaps ["rcOuterStart", "rcInnerStart"] rclass
  [rcOuterStride, rcInnerStride] <-
    newMaps ["rcOuterStride", "rcInnerStride"] rclass

  tA <- newTensor @a "A" [rclass --> rcSize]

  lhs <-
    slice
      ( slice tA $
          Slice
            { start = [rclass --> rcInnerStart],
              end = [rclass --> rcInnerEnd],
              strides = [rclass --> rcInnerStride]
            }
      )
      $ Slice
        { start = [rclass --> rcOuterStart],
          end = [rclass --> rcOuterEnd],
          strides = [rclass --> rcOuterStride]
        }
  precondition [rcOuterStride] $ \[p] -> p .== 1
  precondition [rcInnerStride] $ \[p] -> p .== 1

  rcRhsStart <- combineMap "rcRhsStart" sum [rcOuterStart, rcInnerStart]
  rcRhsEnd <- combineMap "rcRhsEnd" sum [rcOuterEnd, rcInnerStart]
  rhs <-
    slice tA $
      Slice
        { start = [rclass --> rcRhsStart],
          end = [rclass --> rcRhsEnd],
          strides = [rclass --> rcInnerStride]
        }

  rewrite "Slice(Slice(A)) ⇒ Slice(A)" lhs rhs

rule08 :: forall a. AnyDTypeRule a
rule08 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeA, rc0SizeB, rc0Start, rc0End, rc0Stride] <-
    newMaps ["rc0SizeA", "rc0SizeB", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1SizeA, rc1SizeB, rc1Start, rc1End, rc1Stride] <-
    newMaps ["rc1SizeA", "rc1SizeB", "rc1Start", "rc1End", "rc1Stride"] rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0SizeA, rclass1 --> rc1SizeA]
  tB <- newTensor @a "B" [rclass0 --> rc0SizeB, rclass1 --> rc1SizeB]

  lhs <-
    slice (concatTensor tA tB (ByRClass rclass0)) $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          end = [rclass0 --> rc0End, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }
  precondition [rc0SizeA, rc0Start] $ \[a, s] -> a .== s
  precondition [rc0SizeA, rc0SizeB, rc0End] $
    \[a, b, e] -> e .== a + b
  precondition [rc0Stride] $ \[p] -> p .== 1

  rhs <-
    slice tB $
      Slice
        { start = [rclass1 --> rc1Start],
          end = [rclass1 --> rc1End],
          strides = [rclass1 --> rc1Stride]
        }
  rewrite "Slice(Concat(A, B), A.size, A.size + B.size) ⇒ B" lhs rhs

rule09 :: forall a. AnyDTypeRule a
rule09 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  [rc1Size, rc1Start, rc1End, rc1Stride] <-
    newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Stride"] rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size]

  lhs <-
    slice (broadcast tA [rclass1 --> rc1Size]) $
      Slice
        { start = [rclass1 --> rc1Start],
          end = [rclass1 --> rc1End],
          strides = [rclass1 --> rc1Stride]
        }

  rc1NewSize <-
    combineMap "rc1NewSize" (\[s, e, p] -> divOr 0 (e - s + p - 1) p) [rc1Start, rc1End, rc1Stride]
  rhs <- broadcast tA [rclass1 --> rc1NewSize]

  rewrite "Slice(Broadcast(A)) ⇒ Broadcast(A)" lhs rhs

rule10 :: forall a. AnyDTypeRule a
rule10 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeA, rc0SizeB, rc0Start, rc0End, rc0Stride] <-
    newMaps ["rc0SizeA", "rc0SizeB", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1Start, rc1End, rc1Stride] <-
    newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Stride"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0SizeA, rclass1 --> rc1Size]
  tB <- newTensor @a "B" [rclass0 --> rc0SizeB, rclass1 --> rc1Size]
  lhs <-
    slice (concatTensor tA tB (ByRClass rclass0)) $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          end = [rclass0 --> rc0End, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }
  precondition [rc0SizeA, rc0End] $
    \[sz, e] -> e .<= sz

  rhs <-
    slice tA $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          end = [rclass0 --> rc0End, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }

  rewrite "Slice(Concat(A, B)) ⇒ Slice(A)" lhs rhs

rule11 :: forall a. AnyDTypeRule a
rule11 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeA, rc0SizeB, rc0Start, rc0End, rc0Stride] <- newMaps ["rc0SizeA", "rc0SizeB", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1Start, rc1End, rc1Stride] <-
    newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Stride"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0SizeA, rclass1 --> rc1Size]
  tB <- newTensor @a "B" [rclass0 --> rc0SizeB, rclass1 --> rc1Size]
  lhs <-
    slice (concatTensor tA tB (ByRClass rclass0)) $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          end = [rclass0 --> rc0End, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }
  precondition [rc0SizeA, rc0Start] $
    \[sz, s] -> s .>= sz

  rc0StartRhs <- combineMap "rc0StartRhs" (\[s, a] -> s - a) [rc0Start, rc0SizeA]
  rc0EndRhs <- combineMap "rc0EndRhs" (\[e, a] -> e - a) [rc0End, rc0SizeA]
  rhs <-
    slice tB $
      Slice
        { start = [rclass0 --> rc0StartRhs, rclass1 --> rc1Start],
          end = [rclass0 --> rc0EndRhs, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }

  rewrite "Slice(Concat(A, B)) ⇒ Slice(B)" lhs rhs

rule12 :: forall a. AnyDTypeRule a
rule12 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeA, rc0SizeB, rc0SizeC, rc0Start, rc0End, rc0Stride] <-
    newMaps ["rc0SizeA", "rc0SizeB", "rc0SizeC", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1Start, rc1End, rc1Stride] <-
    newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Stride"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0SizeA, rclass1 --> rc1Size]
  tB <- newTensor @a "B" [rclass0 --> rc0SizeB, rclass1 --> rc1Size]
  tC <- newTensor @a "C" [rclass0 --> rc0SizeC, rclass1 --> rc1Size]

  lhs <-
    slice (concatTensorList [tA, tB, tC] (ByRClass rclass0)) $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          end = [rclass0 --> rc0End, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }
  precondition [rc0SizeA, rc0Start] $
    \[sz, s] -> s .>= sz

  rc0StartRhs <- combineMap "rc0StartRhs" (\[s, a] -> s - a) [rc0Start, rc0SizeA]
  rc0EndRhs <- combineMap "rc0EndRhs" (\[e, a] -> e - a) [rc0End, rc0SizeA]
  rhs <-
    slice (concatTensor tB tC (ByRClass rclass0)) $
      Slice
        { start = [rclass0 --> rc0StartRhs, rclass1 --> rc1Start],
          end = [rclass0 --> rc0EndRhs, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }

  rewrite "Slice(Concat(A, B, C)) ⇒ Slice(Concat(B, C))" lhs rhs

rule13 :: forall a. AnyDTypeRule a
rule13 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0End, rc0Stride] <-
    newMaps ["rc0Size", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1Start, rc1End, rc1Stride] <-
    newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Stride"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <-
    slice (reverseTensor tA [ByRClass rclass0]) $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
          end = [rclass0 --> rc0End, rclass1 --> rc1End],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }

  let find_nth s e = divOr 0 (e - s - 1)
  let new_start sz s e p = (sz - s) - (p * find_nth s e p + 1)
  let new_end sz s = sz - s

  rcStartRhs <-
    combineMap "rcStartRhs" (\[sz, s, e, p] -> new_start sz s e p) [rc0Size, rc0Start, rc0End, rc0Stride]
  rcEndRhs <-
    combineMap "rcEndRhs" (\[sz, s] -> new_end sz s) [rc0Size, rc0Start]
  rhs <-
    reverseTensor
      ( slice tA $
          Slice
            { start = [rclass0 --> rcStartRhs, rclass1 --> rc1Start],
              end = [rclass0 --> rcEndRhs, rclass1 --> rc1End],
              strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
            }
      )
      [ByRClass rclass0]

  rewrite "Slice(Reverse(A, dims), start, stride, end) ⇒ Reverse(Slice(A, ...), dims)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  print "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
  print "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  print "############################## rule04 ##############################"
  verifyAnyDTypeDSLWith cvc5 rule04
  print "############################## rule05 ##############################"
  verifyAnyDTypeDSL rule05
  print "############################## rule06 ##############################"
  verifyAnyDTypeDSL rule06
  print "############################## rule07 ##############################"
  verifyAnyDTypeDSL rule07
  print "############################## rule08 ##############################"
  verifyAnyDTypeDSL rule08
  print "############################## rule09 ##############################"
  verifyAnyDTypeDSL rule09
  print "############################## rule10 ##############################"
  verifyAnyDTypeDSL rule10
  print "############################## rule11 ##############################"
  verifyAnyDTypeDSL rule11
  print "############################## rule12 ##############################"
  verifyAnyDTypeDSL rule12
  print "############################## rule13 ##############################"
  verifyAnyDTypeDSLWith cvc5 rule13
