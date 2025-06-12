module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  [rc1SizeA, rc1SizeB] <- newMaps ["rclass1size0", "rclass1size1"] rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1SizeA @@ "label1"]
  tB <- newTensor @a "B" [rclass0 --> rc0Size, rclass1 --> rc1SizeB @@ "label1"]
  lhs <- concatTensorList [tA, tB] (ByLabel "label1")
  rhs <- concatTensor tA tB (ByLabel "label1")
  rewrite "ConcatList(A, B) ⇒ Concat(A, B)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  [rc1SizeA, rc1SizeB, rc1SizeC] <-
    newMaps ["rc1SizeA", "rc1SizeB", "rc1SizeC"] rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1SizeA @@ "label1"]
  tB <- newTensor @a "B" [rclass0 --> rc0Size, rclass1 --> rc1SizeB @@ "label1"]
  tC <- newTensor @a "C" [rclass0 --> rc0Size, rclass1 --> rc1SizeC @@ "label1"]
  lhs <-
    concatTensor
      tA
      (concatTensor tB tC (ByLabel "label1"))
      (ByLabel "label1")
  rhs <-
    concatTensor
      (concatTensor tA tB (ByLabel "label1"))
      tC
      (ByLabel "label1")
  rewrite "Concat(A, Concat(B, C)) ⇒ Concat(Concat(A, B), C)" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  [rc1SizeA, rc1SizeB, rc1SizeC] <-
    newMaps ["rc1SizeA", "rc1SizeB", "rc1SizeC"] rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1SizeA @@ "label1"]
  tB <- newTensor @a "B" [rclass0 --> rc0Size, rclass1 --> rc1SizeB @@ "label1"]
  tC <- newTensor @a "C" [rclass0 --> rc0Size, rclass1 --> rc1SizeC @@ "label1"]
  lhs <- concatTensorList [tA, tB, tC] (ByLabel "label1")
  rhs <-
    concatTensor
      tA
      (concatTensor tB tC (ByLabel "label1"))
      (ByLabel "label1")
  rewrite "ConcatList(A, B, C) ⇒ Concat(A, Concat(B, C))" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0End, rc0Stride] <-
    newMaps ["rc0Start", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1Start1, rc1End1, rc1Start2, rc1End2, rc1Stride] <-
    newMaps ["rc1Size", "rc1Start1", "rc1End1", "rc1Start2", "rc1End2", "rc1Stride"] rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  tA1 <-
    slice tA $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start1],
          end = [rclass0 --> rc0End, rclass1 --> rc1End1],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }
  tA2 <-
    slice tA $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start2],
          end = [rclass0 --> rc0End, rclass1 --> rc1End2],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }
  lhs <- concatTensor tA1 tA2 (ByRClass rclass1)
  precondition [rc1Stride] $ \[p] -> p .== 1
  precondition [rc1End1, rc1Start2] $ \[e, s] -> e .== s

  rhs <-
    slice tA $
      Slice
        { start = [rclass0 --> rc0Start, rclass1 --> rc1Start1],
          end = [rclass0 --> rc0End, rclass1 --> rc1End2],
          strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
        }

  rewrite "Concat(Slice(A), Slice(A)) ⇒ Slice(A)" lhs rhs

rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Low] <- newMaps ["rc0Size", "rc0Low"] rclass0
  rc1Size <- newMap "rc1Size" rclass1

  tB <- newTensor @a "B" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  scalar <- constant @a "a" [rclass0 --> rc0Low, rclass1 --> rc1Size]
  lhs <- concatTensor scalar tB (ByRClass rclass0)

  rc0Zero <- newConstMap "rc0Zero" 0 rclass0
  rhs <-
    pad tB ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low],
          high = [rclass0 --> rc0Zero],
          interior = [rclass0 --> rc0Zero]
        }
  rewrite "Concat(Broadcast(Scalar), B) ⇒ Pad(B, scalar, low)" lhs rhs

rule06 :: forall a. AnyDTypeRule a
rule06 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0High] <- newMaps ["rc0Size", "rc0High"] rclass0
  rc1Size <- newMap "rc1Size" rclass1

  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  scalar <- constant @a "a" [rclass0 --> rc0High, rclass1 --> rc1Size]
  lhs <- concatTensor tA scalar (ByRClass rclass0)

  rc0Zero <- newConstMap "rc0Zero" 0 rclass0
  rhs <-
    pad tA ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Zero],
          high = [rclass0 --> rc0High],
          interior = [rclass0 --> rc0Zero]
        }
  rewrite "Concat(A, Broadcast(Scalar)) ⇒ Pad(A, scalar, high)" lhs rhs

rule07 :: forall a. AnyDTypeRule a
rule07 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  [rc1SizeA, rc1SizeB, rc1SizeC] <- newMaps ["rc1SizeA", "rc1SizeB", "rc1SizeC"] rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1SizeA @@ "label1"]
  tB <- newTensor @a "B" [rclass0 --> rc0Size, rclass1 --> rc1SizeB @@ "label1"]
  tC <- newTensor @a "C" [rclass0 --> rc0Size, rclass1 --> rc1SizeC @@ "label1"]
  lhs <- concatTensor tA (concatTensor tB tC (ByLabel "label1")) (ByLabel "label1")
  rhs <- concatTensorList [tA, tB, tC] (ByLabel "label1")
  rewrite "Concat(A, Concat(B, C)) ⇒ ConcatList(A, B, C)" lhs rhs

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
  print "############################## rule06 ##############################"
  verifyAnyDTypeDSL rule06
  print "############################## rule07 ##############################"
  verifyAnyDTypeDSL rule07
