module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcLow, rcInt, rcHigh] <-
    newMaps ["rcSize", "rcLow", "rcInt", "rcHigh"] rclass

  tA <- newTensor @a "A" [rclass --> rcSize]
  lhs <-
    pad tA ("a" :: a) $
      Padding
        { low = [rclass --> rcLow],
          high = [rclass --> rcHigh],
          interior = [rclass --> rcInt]
        }
  precondition [rcLow] $ \[l] -> l .== 0
  precondition [rcInt] $ \[i] -> i .== 0
  precondition [rcHigh] $ \[h] -> h .== 0

  let rhs = tA
  rewrite "Pad(A, val, 0_0_0) ⇒ A" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Low, rc0Int, rc0High] <-
    newMaps ["rc0Size", "rc0Low", "rc0Int", "rc0High"] rclass0
  [rc1Size, rc1Low, rc1Int, rc1High] <-
    newMaps ["rc1Size", "rc1Low", "rc1Int", "rc1High"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <-
    pad tA ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          high = [rclass0 --> rc0High, rclass1 --> rc1High],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int]
        }
  precondition [rc1Size] $ \[size1] -> size1 .== 1

  rc1NewInt <- newConstMap "rc1NewInt" 0 rclass1
  rhs <-
    pad tA ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          high = [rclass0 --> rc0High, rclass1 --> rc1High],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1NewInt]
        }

  rewrite "Pad(A, val, low_int_high) ⇒ Pad(A, val, low_0_high)" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  [rc0Size, rc0Low, rc0High, rc0Int] <-
    newMaps ["rc0Size", "rc0Low", "rc0High", "rc0Int"] rclass0
  [rc1Size, rc1Low, rc1High, rc1Int] <-
    newMaps ["rc1Size", "rc1Low", "rc1High", "rc1Int"] rclass1
  [rc2Size, rc2Low, rc2High, rc2Int] <-
    newMaps ["rc2Size", "rc2Low", "rc2high", "rc2Int"] rclass2

  tA <- newTensor @a "A" [rclass0 --> rc0Size]

  lhs <-
    pad (broadcast tA [rclass1 --> rc1Size, rclass2 --> rc2Size]) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low, rclass2 --> rc2Low],
          high = [rclass0 --> rc0High, rclass1 --> rc1High, rclass2 --> rc2High],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int, rclass2 --> rc2Int]
        }
  precondition [rc2Int] $ \[i] -> i .== 0
  precondition [rc2Low] $ \[l] -> l .== 0
  precondition [rc2High] $ \[h] -> h .== 0

  rhs <-
    broadcast
      ( pad (broadcast tA [rclass1 --> rc1Size]) ("a" :: a) $
          Padding
            { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
              high = [rclass0 --> rc0High, rclass1 --> rc1High],
              interior = [rclass0 --> rc0Int, rclass1 --> rc1Int]
            }
      )
      [rclass2 --> rc2Size]

  rewrite "Pad(Broadcast(A), v, low_0_0) ⇒ Broadcast(Pad(Broadcast(A), v))" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  -- rclass0: positive low, positive high
  -- rclass1: positive low, negative high
  -- rclass2: negative low, positive high
  -- rclass3: negative low, negative high
  [rclass0, rclass1, rclass2, rclass3] <-
    newRClasses ["rclass0", "rclass1", "rclass2", "rclass3"]
  [rc0Size, rc0Low, rc0High, rc0Int] <-
    newMaps ["rc0Size", "rc0Low", "rc0High", "rc0Int"] rclass0
  [rc1Size, rc1Low, rc1High, rc1Int] <-
    newMaps ["rc1Size", "rc1Low", "rc1High", "rc1Int"] rclass1
  [rc2Size, rc2Low, rc2High, rc2Int] <-
    newMaps ["rc2Size", "rc2Low", "rc2High", "rc2Int"] rclass2
  [rc3Size, rc3Low, rc3High, rc3Int] <-
    newMaps ["rc3Size", "rc3Low", "rc3High", "rc3Int"] rclass3

  tA <-
    newTensor @a
      "A"
      [ rclass0 --> rc0Size,
        rclass1 --> rc1Size,
        rclass2 --> rc2Size,
        rclass3 --> rc3Size
      ]

  lhs <-
    pad tA ("a" :: a) $
      Padding
        { low =
            [ rclass0 --> rc0Low,
              rclass1 --> rc1Low,
              rclass2 --> rc2Low,
              rclass3 --> rc3Low
            ],
          interior =
            [ rclass0 --> rc0Int,
              rclass1 --> rc1Int,
              rclass2 --> rc2Int,
              rclass3 --> rc3Int
            ],
          high =
            [ rclass0 --> rc0High,
              rclass1 --> rc1High,
              rclass2 --> rc2High,
              rclass3 --> rc3High
            ]
        }
  precondition [rc0Int] $ \[i] -> i .== 0
  precondition [rc1Int] $ \[i] -> i .== 0
  precondition [rc2Int] $ \[i] -> i .== 0
  precondition [rc3Int] $ \[i] -> i .== 0
  precondition [rc0Low] $ \[l] -> l .>= 0
  precondition [rc0High] $ \[h] -> h .>= 0
  precondition [rc1Low] $ \[l] -> l .>= 0
  precondition [rc1High] $ \[h] -> h .< 0
  precondition [rc2Low] $ \[l] -> l .< 0
  precondition [rc2High] $ \[h] -> h .>= 0
  precondition [rc3Low] $ \[l] -> l .< 0
  precondition [rc3High] $ \[h] -> h .< 0

  rc1End <-
    combineMap "rc1End" (\[s, l, h] -> s + l + h) [rc1Size, rc1Low, rc1High]
  rc2Start <- combineMap "rc2Start" (\[x] -> abs x) [rc2Low]
  rc3Start <- combineMap "rc3Start" (\[x] -> abs x) [rc3Low]
  rc3End <- combineMap "rc3End" sum [rc3Size, rc3High]
  rhs <-
    slice
      ( pad tA ("a" :: a) $
          Padding
            { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
              interior = [],
              high = [rclass0 --> rc0High, rclass2 --> rc2High]
            }
      )
      $ Slice
        { start = [rclass2 --> rc2Start, rclass3 --> rc3Start],
          end = [rclass1 --> rc1End, rclass3 --> rc3End],
          strides = []
        }

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
