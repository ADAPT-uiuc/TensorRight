module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tP <- newTensor @SymBool "P" [rclass --> map]
  tA <- newTensor @SymBool "A" [rclass --> map]
  tB <- newTensor @SymBool "B" [rclass --> map]
  tC <- newTensor @a "C" [rclass --> map]
  tD <- newTensor @a "D" [rclass --> map]
  lhs <- select (select tP tA tB) tC tD
  rhs <- select (boolBinOp And tP (select tP tA tB)) tC tD
  rewrite "Select(Select(P, A, B), C, D) ==> Select(And(P, Select(P, A, B)), C, D)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeX, rc0SizeY, rc0Low, rc0High] <- newMaps ["rc0SizeX", "rc0SizeY", "rc0Low", "rc0High"] rclass0
  [rc1SizeXY, rc1Low, rc1High, rc1Int] <- newMaps ["rc1SizeXY", "rc1Low", "rc1High", "rc1Int"] rclass1
  rc0Zero <- newConstMap "rc0Zero" 0 rclass0
  tX <- newTensor @a "X" [rclass0 --> rc0SizeX, rclass1 --> rc1SizeXY]
  tY <- newTensor @a "Y" [rclass0 --> rc0SizeY, rclass1 --> rc1SizeXY]
  lhs <-
    pad (concatTensor tX tY (ByRClass rclass0)) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  tXPad <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  tYPad <-
    pad tY ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  rhs <- concatTensor tXPad tYPad (ByRClass rclass0)
  rewrite "Pad(Concatenate(A, B, dim), v, low, high, int) ==> Concatenate(Pad(A, v, low, high, int), Pad(B, v, low, high, int), dim)" lhs rhs

rule02_v1 :: forall a. AnyDTypeRule a
rule02_v1 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeX, rc0SizeY, rc0Low, rc0High] <- newMaps ["rc0SizeX", "rc0SizeY", "rc0Low", "rc0High"] rclass0
  [rc1SizeXY, rc1Low, rc1High, rc1Int] <- newMaps ["rc1SizeXY", "rc1Low", "rc1High", "rc1Int"] rclass1
  rc0Zero <- newConstMap "rc0Zero" 0 rclass0
  tX <- newTensor @a "X" [rclass0 --> rc0SizeX, rclass1 --> rc1SizeXY]
  tY <- newTensor @a "Y" [rclass0 --> rc0SizeY, rclass1 --> rc1SizeXY]
  lhs <-
    pad (concatTensor tX tY (ByRClass rclass0)) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  tXPad <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0Zero, rclass1 --> rc1High]
        }
  tYPad <-
    pad tY ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Zero, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  rhs <- concatTensor tXPad tYPad (ByRClass rclass0)
  rewrite "Pad(Concatenate(A, B, dim), v, low, high, int) ==> Concatenate(Pad(A, v, low, 0, int), Pad(B, v, 0, high, int), dim) if int = 0" lhs rhs

rule02_v2_forward :: forall a. AnyDTypeRule a
rule02_v2_forward _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeX, rc0SizeY, rc0Low, rc0High] <- newMaps ["rc0SizeX", "rc0SizeY", "rc0Low", "rc0High"] rclass0
  [rc1SizeXY, rc1Low, rc1High, rc1Int] <- newMaps ["rc1SizeXY", "rc1Low", "rc1High", "rc1Int"] rclass1
  -- TODO: Generalize to non-zero interior padding
  rc0Zero <- newConstMap "rc0Zero" 0 rclass0
  tX <- newTensor @a "X" [rclass0 --> rc0SizeX, rclass1 --> rc1SizeXY]
  tY <- newTensor @a "Y" [rclass0 --> rc0SizeY, rclass1 --> rc1SizeXY]
  lhs <-
    pad (concatTensor tX tY (ByRClass rclass0)) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  tXPad <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0Zero, rclass1 --> rc1High]
        }
  tYPad <-
    pad tY ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Zero, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  rhs <- concatTensor tXPad tYPad (ByRClass rclass0)
  precondition [rc0SizeX, rc0Low] $ \[s, l] -> s + l .>= 0
  precondition [rc0SizeY, rc0High] $ \[s, h] -> s + h .>= 0
  rewrite "Pad(Concatenate(A, B, dim), v, low, high, int) ==> Concatenate(Pad(A, v, low, 0, int), Pad(B, v, 0, high, int), dim) if int = 0 && low + Shape(A) >= 0 && high + Shape(B) >= 0" lhs rhs

rule02_v2_backward :: forall a. AnyDTypeRule a
rule02_v2_backward _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0SizeX, rc0SizeY, rc0Low, rc0High] <- newMaps ["rc0SizeX", "rc0SizeY", "rc0Low", "rc0High"] rclass0
  [rc1SizeXY, rc1Low, rc1High, rc1Int] <- newMaps ["rc1SizeXY", "rc1Low", "rc1High", "rc1Int"] rclass1
  -- TODO: Generalize to non-zero interior padding
  rc0Zero <- newConstMap "rc0Zero" 0 rclass0
  tX <- newTensor @a "X" [rclass0 --> rc0SizeX, rclass1 --> rc1SizeXY]
  tY <- newTensor @a "Y" [rclass0 --> rc0SizeY, rclass1 --> rc1SizeXY]
  tXPad <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0Zero, rclass1 --> rc1High]
        }
  tYPad <-
    pad tY ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Zero, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  lhs <- concatTensor tXPad tYPad (ByRClass rclass0)
  rhs <-
    pad (concatTensor tX tY (ByRClass rclass0)) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Zero, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  rewrite "Concatenate(Pad(A, v, low, 0, int), Pad(B, v, 0, high, int), dim) ==> Pad(Concatenate(A, B, dim), v, low, high, int) if int = 0" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  print "############################## rule02_v1 ##############################"
  verifyAnyDTypeDSL rule02_v1
  print "############################## rule02_v2_forward ##############################"
  verifyAnyDTypeDSL rule02_v2_forward
  print "############################## rule02_v2_backward ##############################"
  verifyAnyDTypeDSL rule02_v2_backward
