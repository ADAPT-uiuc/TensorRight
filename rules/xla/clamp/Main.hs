module Main (main) where

import Control.Monad.Except (runExceptT)
import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.Core.Tensor.TensorInt (tensorValLt)

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  c1 <- newTensor @a "c1" [rclass --> map]
  c2 <- newTensor @a "c2" [rclass --> map]
  lhs <- clamp c1 (clamp c1 tA c2) c2
  rhs <- clamp c1 tA c2
  rewrite "Clamp(c1, Clamp(c1, A, c2), c2) ⇒ Clamp(c1, A, c2)" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  c1 <- newTensor @a "c1" [rclass --> map]
  c2 <- newTensor @a "c2" [rclass --> map]

  lhs <- numBinOp Max c1 (numBinOp Min tA c2)
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [c1, c2]
    forallIdx
    ( \[vc1, vc2] -> simpleMerge $ do
        u <- runExceptT $ tensorValLt vc1 vc2
        case u of
          Left _ -> con True
          Right v -> return v
    )

  rhs <- clamp c1 tA c2
  rewrite "Max(Broadcast(c1), Min(A, Broadcast(c2))) ⇒ Clamp(c1, A, c2)" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  c1 <- newTensor @a "c1" [rclass --> map]
  c2 <- newTensor @a "c2" [rclass --> map]
  lhs <- numBinOp Min c1 (numBinOp Max tA c2)
  rhs <- clamp c2 tA c1
  rewrite "Min(Broadcast(c1), Max(A, Broadcast(c2))) ⇒ Clamp(c1, A, c2)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
