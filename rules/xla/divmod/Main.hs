module Main (main) where

import Control.Monad.Except (runExceptT)
import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.Core.Tensor.TensorInt (TensorDivMod (tensorDiv))

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  one <- constant @a 1 [rclass --> map]
  lhs <- numBinOp Div tA one
  let rhs = tA
  rewrite "Div(A, 1) ⇒ A" lhs rhs

rule02 :: DSLContext Rewrite
rule02 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @TensorReal "A" [rclass --> map]
  let c = "c" :: TensorReal
  constTensor <- constant @TensorReal c [rclass --> map]
  let creci = tensorDiv 1 "c" :: TensorReal
  constTensorreci <- constant @TensorReal creci [rclass --> map]
  lhs <- numBinOp Div tA constTensor
  rhs <- numBinOp Mul tA constTensorreci
  rewrite "Div(A, Const) ⇒ Mul(A, 1/Const)" lhs rhs

rule03 :: DSLContext Rewrite
rule03 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @TensorReal "A" [rclass --> map]
  tB <- newTensor @TensorReal "B" [rclass --> map]
  tC <- newTensor @TensorReal "C" [rclass --> map]
  tD <- newTensor @TensorReal "D" [rclass --> map]
  lhs <- numBinOp Div (numBinOp Div tA tB) (numBinOp Div tC tD)
  rhs <- numBinOp Div (numBinOp Mul tA tD) (numBinOp Mul tB tC)
  rewrite "Divide(Divide(A, B), Divide(C, D)) ⇒ Divide(Mul(A, D), Mul(B, C))" lhs rhs

rule04 :: DSLContext Rewrite
rule04 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @TensorReal "A" [rclass --> map]
  tB <- newTensor @TensorReal "B" [rclass --> map]
  tC <- newTensor @TensorReal "C" [rclass --> map]
  lhs <- numBinOp Div tA (numBinOp Div tB tC)
  rhs <- numBinOp Div (numBinOp Mul tA tC) tB
  rewrite "Divide(A, Divide(B, C)) ⇒ Divide(Mul(A, C), B)" lhs rhs

rule05 :: DSLContext Rewrite
rule05 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @TensorInt "A" [rclass --> map]
  tB <- newTensor @TensorInt "B" [rclass --> map]
  lhs <- numBinOp Rem (numBinOp Rem tA tB) tB
  rhs <- numBinOp Rem tA tB
  rewrite "Rem(Rem(A, B), B) ⇒ Rem(A, B)" lhs rhs

rule06 :: DSLContext Rewrite
rule06 = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1

  const <- constant @TensorInt "c" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <- numBinOp Rem (iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)) const
  precondition [rc0Size] $ \[s] -> s .<= "c"

  rhs <- iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)
  rewrite "Rem(Iota, Const) ⇒ Iota" lhs rhs

rule07 :: DSLContext Rewrite
rule07 = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1

  let c = "c" :: SymInteger
  const <- constant @TensorInt (nonInf c) [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <- numBinOp Rem (numBinOp Add (iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)) const) const
  precondition [rc0Size] $ \[s] -> c .>= 0

  rhs <- numBinOp Rem (iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)) const
  rewrite "Rem(Add(Iota, Const), Const) ⇒ Rem(Iota, Const)" lhs rhs

rule08 :: DSLContext Rewrite
rule08 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  let xv = "x" :: SymInteger
  let nv = "n" :: SymInteger
  x <- constant @TensorInt (nonInf xv) [rclass --> map]
  n <- constant @TensorInt (nonInf nv) [rclass --> map]
  lhs <- numBinOp Rem (numBinOp Add x n) n
  rhs <- numBinOp Rem x n
  precondition [map] $ \[m] ->
    symIte (xv .>= 0) (xv + nv .>= 0) (xv + nv .< 0)
  rewrite "Rem(Add(X, Const), Const) ⇒ Rem(X, Const)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyDSL rule02
  print "############################## rule03 ##############################"
  verifyDSL rule03
  print "############################## rule04 ##############################"
  verifyDSL rule04
  print "############################## rule05 ##############################"
  verifyDSL rule05
  print "############################## rule06 ##############################"
  verifyDSL rule06
  print "############################## rule07 ##############################"
  verifyDSLWith (withTimeout 10000000 z3) rule07
  print "############################## rule08 ##############################"
  verifyDSLWith (withTimeout 10000000 z3) rule08
