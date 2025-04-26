module Main (main) where

import Control.Monad.Except (runExceptT)
import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.Core.Tensor.TensorInt (tensorValNe)

rule02 :: DSLContext Rewrite
rule02 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @TensorReal "X" [rclass --> map]
  tY <- newTensor @TensorReal "Y" [rclass --> map]
  lhs <- numBinOp Div (numBinOp Mul tX tY) tY
  let rhs = tX
  rewrite "Div(Mul(X, Y), Y) ⇒ X" lhs rhs

rule02_correct :: DSLContext Rewrite
rule02_correct = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @TensorReal "X" [rclass --> map]
  tY <- newTensor @TensorReal "Y" [rclass --> map]
  lhs <- numBinOp Div (numBinOp Mul tX tY) tY
  let rhs = tX
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tY]
    forallIdx
    ( \[y] -> simpleMerge $ do
        u <- runExceptT $ tensorValNe y 0
        case u of
          Left _ -> con True
          Right v -> return v
    )
  rewrite "Div(Mul(X, Y), Y) ⇒ X if Y != 0" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  min <- newTensor @a "Min" [rclass --> map]
  max <- newTensor @a "Max" [rclass --> map]
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- numBinOp Add (clamp min tX max) (clamp min tY max)
  rhs <- clamp min (numBinOp Add tX tY) max
  rewrite "Add(Clamp(Min, X, Max), Clamp(Min, Y, Max)) ==> Clamp(Min, Add(X, Y), Max)" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  [rclass0, rclass1, rclass2] <-
    newRClasses ["rclass0", "rclass1", "rclass2"]
  [rc0sizeX, rc0sizeY] <- newMaps ["rc0sizeX", "rc0sizeY"] rclass0
  rc1size <- newMap "rc1size" rclass1
  rc2size <- newMap "rc2size" rclass2
  tX <- newTensor @a "X" [rclass0 --> rc0sizeX, rclass1 --> rc1size]
  tY <- newTensor @a "Y" [rclass0 --> rc0sizeY, rclass1 --> rc1size]
  lhs <- concatTensor (broadcast tX [rclass2 --> rc2size]) (broadcast tY [rclass2 --> rc2size]) (ByRClass rclass0)
  rhs <- broadcast (concatTensor tX tY (ByRClass rclass0)) [rclass2 --> rc2size]
  rewrite "Concat(Broadcast(X, S), Broadcast(Y, S), dim) ==> Broadcast(Concat(X, Y, dim), S)" lhs rhs

rule08 :: DSLContext Rewrite
rule08 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @TensorReal "X" [rclass --> map]
  tY <- newTensor @TensorReal "Y" [rclass --> map]
  one <- constant @TensorReal "1" [rclass --> map]
  lhs <- numBinOp Div (numBinOp Sub tX tY) tY
  rhs <- numBinOp Sub (numBinOp Div tX tY) one
  rewrite "Div(Sub(X, Y), Y) ⇒ Sub(Div(X, Y), 1)" lhs rhs

rule08_correct :: DSLContext Rewrite
rule08_correct = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @TensorReal "X" [rclass --> map]
  tY <- newTensor @TensorReal "Y" [rclass --> map]
  one <- constant @TensorReal 1 [rclass --> map]
  lhs <- numBinOp Div (numBinOp Sub tX tY) tY
  rhs <- numBinOp Sub (numBinOp Div tX tY) one
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tY]
    forallIdx
    ( \[y] -> simpleMerge $ do
        u <- runExceptT $ tensorValNe y 0
        case u of
          Left _ -> con True
          Right v -> return v
    )
  rewrite "Div(Sub(X, Y), Y) ⇒ Sub(Div(X, Y), 1)" lhs rhs

rule09 :: forall a. NumRule a
rule09 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- numBinOp Add (numBinOp Max tX tY) (numBinOp Max tZ tY)
  rhs <- numBinOp Max (numBinOp Max tX tZ) tY
  rewrite "Add(Max(X, Y), Max(Z, Y)) ==> Max(Max(X, Z), Y)" lhs rhs

rule09_correct :: forall a. NumRule a
rule09_correct _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- numBinOp Max (numBinOp Max tX tY) (numBinOp Max tZ tY)
  rhs <- numBinOp Max (numBinOp Max tX tZ) tY
  rewrite "Max(Max(X, Y), Max(Z, Y)) ==> Max(Max(X, Z), Y)" lhs rhs

main :: IO ()
main = do
  print "############################## rule02 ##############################"
  verifyDSL rule02
  print "############################## rule02_correct ##############################"
  verifyDSL rule02_correct
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule04 ##############################"
  verifyAnyDTypeDSL rule04
  print "############################## rule08 ##############################"
  verifyDSL rule08
  print "############################## rule08_correct ##############################"
  verifyDSL rule08_correct
  print "############################## rule09 ##############################"
  verifyNumDSL rule09
  print "############################## rule09_correct ##############################"
  verifyNumDSL rule09_correct
