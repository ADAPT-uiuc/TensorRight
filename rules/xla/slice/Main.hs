module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, startMap, endMap, strideMap] <-
    newMaps ["sizeMap", "startMap", "endMap", "strideMap"] rclass
  tensor <- newTensor @a "tensor" [rclass --> sizeMap]
  lhs <-
    slice tensor $
      Slice
        { start = [rclass --> startMap],
          end = [rclass --> endMap],
          strides = [rclass --> strideMap]
        }
  let rhs = tensor
  precondition [startMap] $ \[start] -> start .== 0
  precondition [sizeMap, endMap] $ \[size, end] -> end .== size
  precondition [strideMap] $ \[stride] -> stride .== 1
  rewrite "Slice(A) ⇒ A" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  [origSizeMap, newSizeMap, startMap, endMap, strideMap] <- newMaps ["origSizeMap", "newSizeMap", "startMap", "endMap", "strideMap"] rclass
  lhs <- slice (constant @a "a" [rclass --> origSizeMap]) [rclass --> startMap] [rclass --> endMap] [rclass --> strideMap]
  rhs <- constant @a "a" [rclass --> newSizeMap]
  precondition [newSizeMap, startMap, endMap, strideMap] $
    \[newSize, start, end, stride] -> newSize .== divOr 0 (end - start + stride - 1) stride
  rewrite "Slice(Const) ⇒ Const" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMap0, startMap0, endMap0, strideMap0] <- newMaps ["sizeMap0", "startMap0", "endMap0", "strideMap0"] rclass0
  [origSizeMap1, startMap1, endMap1, strideMap1] <- newMaps ["origSizeMap1", "startMap1", "endMap1", "strideMap1"] rclass1
  newSizeMap1 <- newMap "newSizeMap1" rclass1
  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0]
  lhs <- slice (broadcast tensor [rclass1 --> origSizeMap1]) [rclass0 --> startMap0, rclass1 --> startMap1] [rclass0 --> endMap0, rclass1 --> endMap1] [rclass0 --> strideMap0, rclass1 --> strideMap1]
  rhs <- broadcast (slice tensor [rclass0 --> startMap0] [rclass0 --> endMap0] [rclass0 --> strideMap0]) [rclass1 --> newSizeMap1]
  precondition [newSizeMap1, startMap1, endMap1, strideMap1] $
    \[newSize1, start1, end1, stride1] -> newSize1 .== divOr 0 (end1 - start1 + stride1 - 1) stride1
  rewrite "Slice(Broadcast(A)) ⇒ Broadcast(Slice(A))" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, endMap, strideMap] <-
    newMaps ["sizeMap", "endMap", "strideMap"] rclass
  [startMap, lowMap, highMap, intMap] <- newNonNegMaps ["startMap", "lowMap", "highMap", "intMap"] rclass
  tensor <- newTensor @a "tensor" [rclass --> sizeMap]

  lhs <-
    slice
      ( pad tensor ("a" :: a) $
          Padding
            { low = [rclass --> lowMap],
              interior = [rclass --> intMap],
              high = [rclass --> highMap]
            }
      )
      $ Slice
        { start = [rclass --> startMap],
          end = [rclass --> endMap],
          strides = [rclass --> strideMap]
        }
  let rhs = tensor
  precondition [startMap, lowMap] $ \[start, low] -> start .== low
  precondition [strideMap, intMap] $ \[stride, int] -> stride .== int + 1
  precondition [sizeMap, lowMap, intMap, endMap] $
    \[size, low, int, end] -> end .== size + low + (size - 1) * int
  -- TODO: The following precondition is not required since it is already
  -- implied by `highMap` being non-negative. However, removing it leads to
  -- a TIMEOUT
  precondition [highMap] $ \[high] -> high .>= 0
  rewrite "Slice(Pad(A)) ⇒ A" lhs rhs

rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, endMap, strideMap, lowMap, highMap, broadcastMap] <-
    newMaps ["sizeMap", "endMap", "strideMap", "lowMap", "highMap", "broadcastMap"] rclass
  [startMap, intMap] <- newNonNegMaps ["startMap", "intMap"] rclass
  tensor <- newTensor @a "tensor" [rclass --> sizeMap]

  lhs <-
    slice
      ( pad tensor ("a" :: a) $
          Padding
            { low = [rclass --> lowMap],
              interior = [rclass --> intMap],
              high = [rclass --> highMap]
            }
      )
      $ Slice
        { start = [rclass --> startMap],
          end = [rclass --> endMap],
          strides = [rclass --> strideMap]
        }
  rhs <- constant @a "a" [rclass --> broadcastMap]
  precondition [broadcastMap, startMap, endMap, strideMap] $
    \[broadcastSize, start, end, stride] -> broadcastSize .== divOr 0 (end - start + stride - 1) stride
  precondition [sizeMap, startMap, endMap, lowMap, intMap] $
    \[size, start, end, low, int] -> end .<= low .|| start .>= size + low + (size - 1) * int
  rewrite "Slice(Pad(A, v)) ⇒ Broadcast(v)" lhs rhs

rule06 :: forall a. AnyDTypeRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  [startMap, endMap, lowMap, highMap] <-
    newNonNegMaps ["startMap", "endMap", "lowMap", "highMap"] rclass
  strideMap <- newConstMap "strideMap" 1 rclass
  intMap <- newConstMap "intMap" 0 rclass
  newStartMap <- combineMap "newStartMap" (\[a, b] -> a - b) [startMap, lowMap]
  newEndMap <- combineMap "newEndMap" (\[a, b] -> a - b) [endMap, lowMap]
  tensor <- newTensor @a "tensor" [rclass --> sizeMap]

  lhs <-
    slice
      ( pad tensor ("a" :: a) $
          Padding
            { low = [rclass --> lowMap],
              interior = [rclass --> intMap],
              high = [rclass --> highMap]
            }
      )
      $ Slice
        { start = [rclass --> startMap],
          end = [rclass --> endMap],
          strides = [rclass --> strideMap]
        }

  rhs <-
    slice tensor $
      Slice
        { start = [rclass --> newStartMap],
          end = [rclass --> newEndMap],
          strides = [rclass --> strideMap]
        }
  precondition [startMap, lowMap] $ \[start, low] -> start .>= low
  precondition [sizeMap, endMap, lowMap, intMap] $
    \[size, end, low, int] -> end .<= size + low + (size - 1) * int
  rewrite "Slice(Pad(A, v)) ⇒ Slice(A)" lhs rhs

rule07 :: forall a. AnyDTypeRule a
rule07 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMap0, endMap0, innerEnd0] <- newMaps ["sizeMap0", "endMap0", "innerEnd0"] rclass0
  [startMap0, innerStart0] <- newNonNegMaps ["startMap0", "innerStart0"] rclass0
  [sizeMap1, endMap1, innerEnd1] <- newMaps ["sizeMap1", "endMap1", "innerEnd1"] rclass1
  [startMap1, innerStart1] <- newNonNegMaps ["startMap1", "innerStart1"] rclass1
  rhsStart0 <- combineMap "rhsStart0" (\[a, b] -> a + b) [startMap0, innerStart0]
  rhsStart1 <- combineMap "rhsStart1" (\[a, b] -> a + b) [startMap1, innerStart1]
  rhsEnd0 <- combineMap "rhsEnd0" (\[a, b] -> a + b) [innerEnd0, startMap0]
  rhsEnd1 <- combineMap "rhsEnd1" (\[a, b] -> a + b) [innerEnd1, startMap1]
  strideMap0 <- newConstMap "strideMap0" 1 rclass0
  strideMap1 <- newConstMap "strideMap1" 1 rclass1

  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0, rclass1 --> sizeMap1]

  lhs <-
    slice
      ( slice tensor $
          Slice
            { start = [rclass0 --> startMap0, rclass1 --> startMap1],
              end = [rclass0 --> endMap0, rclass1 --> endMap1],
              strides = [rclass0 --> strideMap0, rclass1 --> strideMap1]
            }
      )
      $ Slice
        { start = [rclass0 --> innerStart0, rclass1 --> innerStart1],
          end = [rclass0 --> innerEnd0, rclass1 --> innerEnd1],
          strides = [rclass0 --> strideMap0, rclass1 --> strideMap1]
        }
  rhs <-
    slice tensor $
      Slice
        { start = [rclass0 --> rhsStart0, rclass1 --> rhsStart1],
          end = [rclass0 --> rhsEnd0, rclass1 --> rhsEnd1],
          strides = [rclass0 --> strideMap0, rclass1 --> strideMap1]
        }

  rewrite "Slice(Slice(A)) ⇒ Slice(A)" lhs rhs

rule08 :: forall a. AnyDTypeRule a
rule08 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMapA0, sizeMapB0, endMap0, strideMap0] <- newMaps ["sizeMapA0", "sizeMapB0", "endMap0", "strideMap0"] rclass0
  startMap0 <- newNonNegMap "startMap0" rclass0
  [sizeMapA1, sizeMapB1, endMap1, strideMap1] <- newMaps ["sizeMapA1", "sizeMapB1", "endMap1", "strideMap1"] rclass1
  startMap1 <- newNonNegMap "startMap1" rclass1
  tensorA <- newTensor @a "tensorA" [rclass0 --> sizeMapA0, rclass1 --> sizeMapA1]
  tensorB <- newTensor @a "tensorB" [rclass0 --> sizeMapB0, rclass1 --> sizeMapB1]

  lhs <-
    slice (concatTensor tensorA tensorB (ByRClass rclass0)) $
      Slice
        { start = [rclass0 --> startMap0, rclass1 --> startMap1],
          end = [rclass0 --> endMap0, rclass1 --> endMap1],
          strides = [rclass0 --> strideMap0, rclass1 --> strideMap1]
        }
  let rhs = tensorB

  precondition [startMap1] $ \[start1] -> start1 .== 0
  precondition [sizeMapA1, endMap1] $ \[sizeA1, end1] -> end1 .== sizeA1
  precondition [strideMap0] $ \[stride0] -> stride0 .== 1
  precondition [strideMap1] $ \[stride1] -> stride1 .== 1
  precondition [sizeMapA0, startMap0] $ \[sizeA0, start0] -> start0 .== sizeA0
  precondition [sizeMapA0, sizeMapB0, endMap0] $
    \[sizeA0, sizeB0, end0] -> end0 .== sizeA0 + sizeB0

  rewrite "Slice(Concat(A,B), A.size, A.size+B.size) ⇒ B" lhs rhs

rule09 :: forall a. AnyDTypeRule a
rule09 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMap0, startMap0, endMap0, strideMap0] <-
    newMaps ["sizeMap0", "startMap0", "endMap0", "strideMap0"] rclass0
  [sizeMap1, startMap1, endMap1, strideMap1, broadcastSize1] <-
    newMaps ["sizeMap1", "startMap1", "endMap1", "strideMap1", "broadcastSize1"] rclass1
  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0]

  lhs <-
    slice (broadcast tensor [rclass1 --> sizeMap1]) $
      Slice
        { start = [rclass0 --> startMap0, rclass1 --> startMap1],
          end = [rclass0 --> endMap0, rclass1 --> endMap1],
          strides = [rclass0 --> strideMap0, rclass1 --> strideMap1]
        }
  rhs <- broadcast tensor [rclass1 --> broadcastSize1]

  precondition [startMap0] $ \[s] -> s .== 0
  precondition [endMap0, sizeMap0] $ \[e, s] -> e .== s
  precondition [strideMap0] $ \[p] -> p .== 1
  precondition [broadcastSize1, startMap1, endMap1, strideMap1] $
    \[b, s, e, p] -> b .== divOr 0 (e - s + p - 1) p

  rewrite "Slice(Broadcast(A)) ⇒ Broadcast(A)" lhs rhs

rule10 :: forall a. AnyDTypeRule a
rule10 _ = do
  rclass <- newRClass "rclass"
  [sizeMapA, sizeMapB, endMap] <- newMaps ["sizeMapA", "sizeMapB", "endMap"] rclass
  startMap <- newNonNegMap "startMap" rclass
  strideMap <- newConstMap "strideMap" 1 rclass
  tensorA <- newTensor @a "tensorA" [rclass --> sizeMapA]
  tensorB <- newTensor @a "tensorB" [rclass --> sizeMapB]

  lhs <-
    slice (concatTensor tensorA tensorB (ByRClass rclass)) $
      Slice
        { start = [rclass --> startMap],
          end = [rclass --> endMap],
          strides = [rclass --> strideMap]
        }
  rhs <-
    slice tensorA $
      Slice
        { start = [rclass --> startMap],
          end = [rclass --> endMap],
          strides = [rclass --> strideMap]
        }

  precondition [sizeMapA, endMap] $
    \[sizeA, end] -> end .<= sizeA

  rewrite "Slice(Concat(A,B)) ⇒ Slice(A)" lhs rhs

rule11 :: forall a. AnyDTypeRule a
rule11 _ = do
  rclass <- newRClass "rclass"
  [sizeMapA, sizeMapB, endMap] <- newMaps ["sizeMapA", "sizeMapB", "endMap"] rclass
  startMap <- newNonNegMap "startMap" rclass
  startMapB <- combineMap "startMapB" (\[a, b] -> a - b) [startMap, sizeMapA]
  endMapB <- combineMap "endMapB" (\[a, b] -> a - b) [endMap, sizeMapA]
  strideMap <- newConstMap "strideMap" 1 rclass
  tensorA <- newTensor @a "tensorA" [rclass --> sizeMapA]
  tensorB <- newTensor @a "tensorB" [rclass --> sizeMapB]

  lhs <-
    slice (concatTensor tensorA tensorB (ByRClass rclass)) $
      Slice
        { start = [rclass --> startMap],
          end = [rclass --> endMap],
          strides = [rclass --> strideMap]
        }
  rhs <-
    slice tensorB $
      Slice
        { start = [rclass --> startMapB],
          end = [rclass --> endMapB],
          strides = [rclass --> strideMap]
        }

  precondition [sizeMapA, startMap] $
    \[sizeA, start] -> start .> sizeA

  rewrite "Slice(Concat(A,B)) ⇒ Slice(B)" lhs rhs

rule12 :: forall a. AnyDTypeRule a
rule12 _ = do
  rclass <- newRClass "rclass"
  [sizeMapA, sizeMapB, sizeMapC, startMap, endMap, strideMap] <-
    newMaps ["sizeMapA", "sizeMapB", "sizeMapC", "startMap", "endMap", "strideMap"] rclass
  startMapB <- combineMap "startMapB" (\[a, b] -> a - b) [startMap, sizeMapA]
  endMapB <- combineMap "endMapB" (\[a, b] -> a - b) [endMap, sizeMapA]

  tensorA <- newTensor @a "tensorA" [rclass --> sizeMapA]
  tensorB <- newTensor @a "tensorB" [rclass --> sizeMapB]
  tensorC <- newTensor @a "tensorC" [rclass --> sizeMapC]

  lhs <-
    slice (concatTensorList [tensorA, tensorB, tensorC] (ByRClass rclass)) $
      Slice
        { start = [rclass --> startMap],
          end = [rclass --> endMap],
          strides = [rclass --> strideMap]
        }
  rhs <-
    slice (concatTensor tensorB tensorC (ByRClass rclass)) $
      Slice
        { start = [rclass --> startMapB],
          end = [rclass --> endMapB],
          strides = [rclass --> strideMap]
        }

  precondition [sizeMapA, startMap] $ \[sizeA, start] -> sizeA .<= start

  rewrite "Slice(Concat(A,B,C)) ⇒ Slice(Concat(B,C))" lhs rhs

rule13 :: forall a. AnyDTypeRule a
rule13 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, startMapLhs, endMapLhs, strideMap, startMapRhs, endMapRhs] <-
    newMaps ["sizeMap", "startMapLhs", "endMapLhs", "strideMap", "startMapRhs", "endMapRhs"] rclass
  tensor <- newTensor @a "tensor" [rclass --> sizeMap]

  lhs <-
    slice (reverseTensor tensor [ByRClass rclass]) $
      Slice
        { start = [rclass --> startMapLhs],
          end = [rclass --> endMapLhs],
          strides = [rclass --> strideMap]
        }
  rhs <-
    reverseTensor
      ( slice tensor $
          Slice
            { start = [rclass --> startMapRhs],
              end = [rclass --> endMapRhs],
              strides = [rclass --> strideMap]
            }
      )
      [ByRClass rclass]

  let find_nth start end = divOr 0 (end - start)
  let count start end stride =
        symIte
          (modOr 0 (end - start) stride .== 0)
          (find_nth start end stride - 1)
          (find_nth start end stride)
  let new_start size start end stride = start + stride * count start end stride + 1 - size
  let new_end size start end stride =
        symIte
          (size .>= new_start size start end stride + end - start)
          (new_start size start end stride + end - start)
          size

  precondition [sizeMap, startMapLhs, endMapLhs, strideMap, startMapRhs] $
    \[size, startLhs, endLhs, stride, startRhs] -> startRhs .== new_start size startLhs endLhs stride
  precondition [sizeMap, startMapLhs, endMapLhs, strideMap, endMapRhs] $
    \[size, startLhs, endLhs, stride, endRhs] -> endRhs .== new_end size startLhs endLhs stride

  rewrite "Slice(Reverse(A,dims),start,stride,end) ⇒ Reverse(Slice(A,...),dims)" lhs rhs

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
  verifyAnyDTypeDSLWith (withTimeout 10000000 z3) rule13
