module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [sizeMap, lowMap, interiorMap, highMap] <- newMaps ["sizeMap", "lowMap", "interiorMap", "highMap"] rclass
  tensor <- newTensor @a "tensor" [rclass --> sizeMap]
  lhs <- pad tensor ("a" :: a) [rclass --> lowMap] [rclass --> interiorMap] [rclass --> highMap]
  let rhs = tensor
  precondition [lowMap] $ \[low] -> low .== 0
  precondition [interiorMap] $ \[interior] -> interior .== 0
  precondition [highMap] $ \[high] -> high .== 0
  rewrite "Pad(A,val, 0_0_0) ⇒ A" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMap0, lowMap0, interiorMap0, highMap0] <- newMaps ["sizeMap0", "lowMap0", "interiorMap0", "highMap0"] rclass0
  [sizeMap1, lowMap1, interiorMap1lhs, interiorMap1rhs, highMap1] <- newMaps ["sizeMap1", "lowMap1", "interiorMap1lhs", "interiorMap1rhs", "highMap1"] rclass1
  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0, rclass1 --> sizeMap1]
  lhs <- pad tensor ("a" :: a) [rclass0 --> lowMap0, rclass1 --> lowMap1] [rclass0 --> interiorMap0, rclass1 --> interiorMap1lhs] [rclass0 --> highMap0, rclass1 --> highMap1]
  rhs <- pad tensor ("a" :: a) [rclass0 --> lowMap0, rclass1 --> lowMap1] [rclass0 --> interiorMap0, rclass1 --> interiorMap1rhs] [rclass0 --> highMap0, rclass1 --> highMap1]
  precondition [interiorMap1rhs] $ \[interior1rhs] -> interior1rhs .== 0
  precondition [sizeMap1] $ \[size1] -> size1 .== 1
  rewrite "Pad(A,val, low_int_high) ⇒ Pad(A,val,low_0_high)" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  [sizeMap0, lowMap0, highMap0] <- newMaps ["sizeMap0", "lowMap0", "highMap0"] rclass0
  [sizeMap1, lowMap1, highMap1] <- newMaps ["sizeMap1", "lowMap1", "highMap1"] rclass1
  [sizeMap2, lowMap2, highMap2] <- newMaps ["sizeMap2", "lowMap2", "highMap2"] rclass2
  intMap0 <- newConstMap "intMap0" 0 rclass0
  intMap1 <- newConstMap "intMap1" 0 rclass1
  intMap2 <- newConstMap "intMap2" 0 rclass2

  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0]

  lhs <-
    pad (broadcast tensor [rclass1 --> sizeMap1, rclass2 --> sizeMap2]) ("a" :: a) $
      Padding
        { low = [rclass0 --> lowMap0, rclass1 --> lowMap1, rclass2 --> lowMap2],
          interior = [rclass0 --> intMap0, rclass1 --> intMap1, rclass2 --> intMap2],
          high = [rclass0 --> highMap0, rclass1 --> highMap1, rclass2 --> highMap2]
        }
  rhs <-
    broadcast
      ( pad (broadcast tensor [rclass1 --> sizeMap1]) ("a" :: a) $
          Padding
            { low = [rclass0 --> lowMap0, rclass1 --> lowMap1],
              interior = [rclass0 --> intMap0, rclass1 --> intMap1],
              high = [rclass0 --> highMap0, rclass1 --> highMap1]
            }
      )
      [rclass2 --> sizeMap2]

  precondition [lowMap2] $ \[low2] -> low2 .== 0
  precondition [highMap2] $ \[high2] -> high2 .== 0

  rewrite "Pad(Broadcast(Const1), Const2, low_0_0) ⇒ Broadcast(Pad(Broadcast(Const1), Const2))" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [sizeMap0, lowMap0, highMap0, startMap0, endMap0] <- newMaps ["sizeMap0", "lowMap0", "highMap0", "startMap0", "endMap0"] rclass0
  [sizeMap1, lowMap1, highMap1, startMap1, endMap1] <- newMaps ["sizeMap1", "lowMap1", "highMap1", "startMap1", "endMap1"] rclass1
  intMap0 <- newConstMap "intMap0" 0 rclass0
  intMap1 <- newConstMap "intMap1" 0 rclass1
  strideMap0 <- newConstMap "strideMap0" 1 rclass0
  strideMap1 <- newConstMap "strideMap1" 1 rclass1
  lowMapRhs <- newConstMap "lowMapRhs" 0 rclass0
  highMapRhs <- newConstMap "highMapRhs" 0 rclass0

  tensor <- newTensor @a "tensor" [rclass0 --> sizeMap0, rclass1 --> sizeMap1]

  lhs <-
    pad tensor ("a" :: a) $
      Padding
        { low = [rclass0 --> lowMap0, rclass1 --> lowMap1],
          interior = [rclass0 --> intMap0, rclass1 --> intMap1],
          high = [rclass0 --> highMap0, rclass1 --> highMap1]
        }
  rhs <-
    slice
      ( pad tensor ("a" :: a) $
          Padding
            { low = [rclass0 --> lowMapRhs, rclass1 --> lowMap1],
              interior = [rclass0 --> intMap0, rclass1 --> intMap1],
              high = [rclass0 --> highMapRhs, rclass1 --> highMap1]
            }
      )
      $ Slice
        { start = [rclass0 --> startMap0, rclass1 --> startMap1],
          end = [rclass0 --> endMap0, rclass1 --> endMap1],
          strides = [rclass0 --> strideMap0, rclass1 --> strideMap1]
        }

  precondition [lowMap0] $ \[low0] -> low0 .< 0
  precondition [highMap0] $ \[high0] -> high0 .< 0
  precondition [lowMap1] $ \[low1] -> low1 .>= 0
  precondition [highMap1] $ \[high1] -> high1 .>= 0
  precondition [startMap0, lowMap0] $ \[start0, low0] -> start0 .== abs low0
  precondition [sizeMap0, endMap0, highMap0] $ \[size0, end0, high0] -> end0 .== size0 + high0
  precondition [startMap1] $ \[start1] -> start1 .== 0
  precondition [sizeMap1, endMap1, lowMap1, highMap1] $ \[size1, end1, low1, high1] -> end1 .== size1 + low1 + high1

  rewrite "Pad(A, val, negative_negative) ⇒ Slice(Pad(A, val, 0_0), abs(negative),negative+size)" lhs rhs

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
