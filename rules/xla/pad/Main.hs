module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcLow, rcInt, rcHigh] <- newMaps ["rcSize", "rcLow", "rcInt", "rcHigh"] rclass

  tA <- newTensor @a "A" [rclass --> rcSize]
  lhs <- pad tA ("a" :: a) $
    Padding {
      low = [rclass --> rcLow],
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
  [rc0Size, rc0Low, rc0Int, rc0High] <- newMaps ["rc0Size", "rc0Low", "rc0Int", "rc0High"] rclass0
  [rc1Size, rc1Low, rc1Int, rc1High] <- newMaps ["rc1Size", "rc1Low", "rc1Int", "rc1High"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <- pad tA ("a" :: a) $
    Padding {
      low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
      high = [rclass0 --> rc0High, rclass1 --> rc1High],
      interior = [rclass0 --> rc0Int, rclass1 --> rc1Int]
    }
  precondition [rc1Size] $ \[size1] -> size1 .== 1

  rc1NewInt <- newConstMap "rc1NewInt" 0 rclass1
  rhs <- pad tA ("a" :: a) $
    Padding {
      low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
      high = [rclass0 --> rc0High, rclass1 --> rc1High],
      interior = [rclass0 --> rc0Int, rclass1 --> rc1NewInt]
    }

  rewrite "Pad(A, val, low_int_high) ⇒ Pad(A, val, low_0_high)" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  [rc0Size, rc0Low, rc0High, rc0Int] <- newMaps ["rc0Size", "rc0Low", "rc0High", "rc0Int"] rclass0
  [rc1Size, rc1Low, rc1High, rc1Int] <- newMaps ["rc1Size", "rc1Low", "rc1High", "rc1Int"] rclass1
  [rc2Size, rc2Low, rc2High, rc2Int] <- newMaps ["rc2Size", "rc2Low", "rc2high", "rc2Int"] rclass2

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
  -- TODO: There should be 4 rclasses: combination of the signs of the
  -- low and high paddings.
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Low, rc0High, rc0Int] <- newMaps ["rc0Size", "rc0Low", "rc0High", "rc0Int"] rclass0
  [rc1Size, rc1Low, rc1High, rc1Int] <- newMaps ["rc1Size", "rc1Low", "rc1High", "rc1Int"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]

  lhs <-
    pad tA ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  precondition [rc0Int] $ \[i] -> i .== 0
  precondition [rc1Int] $ \[i] -> i .== 0
  precondition [rc0Low] $ \[low0] -> low0 .< 0
  precondition [rc0High] $ \[high0] -> high0 .< 0
  precondition [rc1Low] $ \[low1] -> low1 .>= 0
  precondition [rc1High] $ \[high1] -> high1 .>= 0

  rc0Start <- combineMap "rc0Start" (\[x] -> abs x) [rc0Low]
  rc0End <- combineMap "rc0End" sum [rc0Size, rc0High]
  rc0Stride <- newConstMap "rc0Stride" 1 rclass0
  rhs <-
    slice
      ( pad tA ("a" :: a) $
          Padding
            { low = [rclass1 --> rc1Low],
              interior = [rclass1 --> rc1Int],
              high = [rclass1 --> rc1High]
            }
      )
      $ Slice
        { start = [rclass0 --> rc0Start],
          end = [rclass0 --> rc0End],
          strides = [rclass0 --> rc0Stride]
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
