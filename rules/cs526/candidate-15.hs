module Main (main) where

import qualified Data.Text as T
import Grisette hiding (dot, (-->))
import TensorRight

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- numBinOp Max (numBinOp Mul tX tZ) (numBinOp Mul tY tZ)
  rhs <- numBinOp Mul (numBinOp Max tX tY) tZ
  rewrite "Max(Mul(X, Z), Mul(Y, Z)) ==> Mul(Max(X, Y), Z)" lhs rhs

rule02_v1 :: forall a. NumRule a
rule02_v1 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- numBinOp Max (numBinOp Add tX tZ) (numBinOp Add tY tZ)
  rhs <- numBinOp Add (numBinOp Max tX tY) tZ
  rewrite "Max(Add(X, Z), Add(Y, Z)) ==> Add(Max(X, Y), Z)" lhs rhs

rule02_v2 :: forall a. NumRule a
rule02_v2 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- numBinOp Max (numBinOp Sub tX tZ) (numBinOp Sub tY tZ)
  rhs <- numBinOp Sub (numBinOp Max tX tY) tZ
  rewrite "Max(Sub(X, Z), Sub(Y, Z)) ==> Sub(Max(X, Y), Z)" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  geXY <- compareOp Ge tX tY
  ltXY <- compareOp Lt tX tY
  tP <- boolBinOp And (boolUnaryOp Not geXY) (boolUnaryOp Not ltXY)
  lhs <- select tP tX tY
  let rhs = tX
  rewrite "select(And(Not(Ge(X, Y)), Not(Lt(X, Y))), X, Y) ==> X" lhs rhs

rule03_v1 :: forall a. NumRule a
rule03_v1 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  geXY <- compareOp Ge tX tY
  ltXY <- compareOp Lt tX tY
  tP <- boolBinOp And (boolUnaryOp Not geXY) (boolUnaryOp Not ltXY)
  lhs <- select tP tX tY
  let rhs = tY
  rewrite "select(And(Not(Ge(X, Y)), Not(Lt(X, Y))), X, Y) ==> Y" lhs rhs

constructRule :: forall a. T.Text -> CompareOp -> CompareOp -> NumRule a
constructRule name op1 op2 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- boolUnaryOp Not (compareOp op1 tX tY)
  rhs <- compareOp op2 tX tY
  rewrite name lhs rhs

rule03_not_ge :: forall a. NumRule a
rule03_not_ge = constructRule "Not(Ge(X, Y)) ==> Lt(X, Y)" Ge Lt

rule03_not_le :: forall a. NumRule a
rule03_not_le = constructRule "Not(Le(X, Y)) ==> Gt(X, Y)" Le Gt

rule03_not_eq :: forall a. NumRule a
rule03_not_eq = constructRule "Not(Eq(X, Y)) ==> Ne(X, Y)" Eqv Ne

rule03_not_ne :: forall a. NumRule a
rule03_not_ne = constructRule "Not(Ne(X, Y)) ==> Eq(X, Y)" Ne Eqv

rule03_not_gt :: forall a. NumRule a
rule03_not_gt = constructRule "Not(Gt(X, Y)) ==> Le(X, Y)" Gt Le

rule03_not_lt :: forall a. NumRule a
rule03_not_lt = constructRule "Not(Lt(X, Y)) ==> Ge(X, Y)" Lt Ge

rule03_and_not :: DSLContext Rewrite
rule03_and_not = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @SymBool "X" [rclass --> map]
  lhs <- boolBinOp And tX (boolUnaryOp Not tX)
  rhs <- constant @SymBool (con False) [rclass --> map]
  rewrite "And(X, Not(X)) ==> False" lhs rhs

rule03_or_not :: DSLContext Rewrite
rule03_or_not = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @SymBool "X" [rclass --> map]
  lhs <- boolBinOp Or tX (boolUnaryOp Not tX)
  rhs <- constant @SymBool (con True) [rclass --> map]
  rewrite "Or(X, Not(X)) ==> True" lhs rhs

rule03_and :: DSLContext Rewrite
rule03_and = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @SymBool "X" [rclass --> map]
  lhs <- boolBinOp And tX tX
  let rhs = tX
  rewrite "And(X, X) ==> X" lhs rhs

rule03_or :: DSLContext Rewrite
rule03_or = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @SymBool "X" [rclass --> map]
  lhs <- boolBinOp Or tX tX
  let rhs = tX
  rewrite "Or(X, X) ==> X" lhs rhs

rule04 :: DSLContext Rewrite
rule04 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @SymBool "X" [rclass --> map]
  tY <- newTensor @SymBool "Y" [rclass --> map]
  lhs <- boolBinOp And (boolUnaryOp Not (boolBinOp And tX tY)) tY
  rhs <- boolBinOp And (boolUnaryOp Not tY) tX
  rewrite "And(Not(And(X, Y)), Y) ==> And(Not(Y), X)" lhs rhs

rule04_v1 :: DSLContext Rewrite
rule04_v1 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @SymBool "X" [rclass --> map]
  tY <- newTensor @SymBool "Y" [rclass --> map]
  lhs <- boolBinOp And (boolUnaryOp Not (boolBinOp And tX tY)) tY
  rhs <- boolBinOp And (boolUnaryOp Not tX) tY
  rewrite "And(Not(And(X, Y)), Y) ==> And(Not(X), Y)" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- numBinOp Max (select (compareOp Ge tX tY) tX tY) (select (compareOp Lt tX tY) tX tY)
  rhs <- numBinOp Max tX tY
  rewrite "Max(Select(Ge(X, Y), X, Y), Select(Lt(X, Y), X, Y)) ==> Max(X, Y)" lhs rhs

rule05_v1 :: forall a. NumRule a
rule05_v1 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- select (compareOp Ge tX tY) tX tY
  rhs <- numBinOp Max tX tY
  rewrite "Select(Ge(X, Y), X, Y) ==> Max(X, Y)" lhs rhs

rule05_v2 :: forall a. NumRule a
rule05_v2 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- select (compareOp Lt tX tY) tX tY
  rhs <- numBinOp Min tX tY
  rewrite "Select(Lt(X, Y), X, Y) ==> Min(X, Y)" lhs rhs

rule05_v3 :: forall a. NumRule a
rule05_v3 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- numBinOp Max (numBinOp Max tX tY) (numBinOp Min tX tY)
  rhs <- numBinOp Max tX tY
  rewrite "Max(Max(X, Y), Min(X, Y)) ==> Max(X, Y)" lhs rhs

rule05_v4 :: forall a. NumRule a
rule05_v4 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- numBinOp Min (numBinOp Max tX tY) (numBinOp Min tX tY)
  rhs <- numBinOp Min tX tY
  rewrite "Min(Max(X, Y), Min(X, Y)) ==> Min(X, Y)" lhs rhs

rule06_forward :: forall a. NumRule a
rule06_forward _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tP <- newTensor @SymBool "P" [rclass --> map]
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  tW <- newTensor @a "W" [rclass --> map]
  lhs <- numBinOp Add (select tP tX tY) (select tP tZ tW)
  rhs <- select tP (numBinOp Add tX tZ) (numBinOp Add tY tW)
  rewrite "Add(Select(P, X, Y), Select(P, Z, W)) ==> Select(P, Add(X, Z), Add(Y, W))" lhs rhs

rule06_backward :: forall a. NumRule a
rule06_backward _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tP <- newTensor @SymBool "P" [rclass --> map]
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  tW <- newTensor @a "W" [rclass --> map]
  lhs <- select tP (numBinOp Add tX tZ) (numBinOp Add tY tW)
  rhs <- numBinOp Add (select tP tX tY) (select tP tZ tW)
  rewrite "Select(P, Add(X, Z), Add(Y, W)) ==> Add(Select(P, X, Y), Select(P, Z, W))" lhs rhs

rule08 :: forall a. NumRule a
rule08 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- numBinOp Mul (numBinOp Max tX tY) (numBinOp Min tX tY)
  rhs <- numBinOp Mul tX tY
  rewrite "Mul(Max(X, Y), Min(X, Y)) ==> Mul(X, Y)" lhs rhs

rule09_forward :: forall a. NumRule a
rule09_forward _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcLength] <- newMaps ["rcSize", "rcStart", "rcLength"] rclass
  tX <- newTensor @a "X" [rclass --> rcSize]
  tY <- newTensor @a "Y" [rclass --> rcSize]
  let dynamicSliceConfig =
        DySlice
          { start = [rclass --> rcStart],
            sizes = [rclass --> rcLength]
          }
  lhs <- numBinOp Add (dynamicSlice tX dynamicSliceConfig) (dynamicSlice tY dynamicSliceConfig)
  rhs <- dynamicSlice (numBinOp Add tX tY) dynamicSliceConfig
  rewrite "Add(DynamicSlice(X, I, S), DynamicSlice(Y, I, S)) ==> DynamicSlice(Add(X, Y), I, S)" lhs rhs

rule09_backward :: forall a. NumRule a
rule09_backward _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcLength] <- newMaps ["rcSize", "rcStart", "rcLength"] rclass
  tX <- newTensor @a "X" [rclass --> rcSize]
  tY <- newTensor @a "Y" [rclass --> rcSize]
  let dynamicSliceConfig =
        DySlice
          { start = [rclass --> rcStart],
            sizes = [rclass --> rcLength]
          }
  lhs <- dynamicSlice (numBinOp Add tX tY) dynamicSliceConfig
  rhs <- numBinOp Add (dynamicSlice tX dynamicSliceConfig) (dynamicSlice tY dynamicSliceConfig)
  rewrite "DynamicSlice(Add(X, Y), I, S) ==> Add(DynamicSlice(X, I, S), DynamicSlice(Y, I, S))" lhs rhs

rule09_slice_forward :: forall a. NumRule a
rule09_slice_forward _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcEnd, rcStride] <- newMaps ["rcSize", "rcStart", "rcEnd", "rcStride"] rclass
  tX <- newTensor @a "X" [rclass --> rcSize]
  tY <- newTensor @a "Y" [rclass --> rcSize]
  let sliceConfig =
        Slice
          { start = [rclass --> rcStart],
            end = [rclass --> rcEnd],
            strides = [rclass --> rcStride]
          }
  lhs <- numBinOp Add (slice tX sliceConfig) (slice tY sliceConfig)
  rhs <- slice (numBinOp Add tX tY) sliceConfig
  rewrite "Add(Slice(X, S, E, P), Slice(Y, S, E, P)) ==> Slice(Add(X, Y), S, E, P)" lhs rhs

rule09_slice_backward :: forall a. NumRule a
rule09_slice_backward _ = do
  rclass <- newRClass "rclass"
  [rcSize, rcStart, rcEnd, rcStride] <- newMaps ["rcSize", "rcStart", "rcEnd", "rcStride"] rclass
  tX <- newTensor @a "X" [rclass --> rcSize]
  tY <- newTensor @a "Y" [rclass --> rcSize]
  let sliceConfig =
        Slice
          { start = [rclass --> rcStart],
            end = [rclass --> rcEnd],
            strides = [rclass --> rcStride]
          }
  lhs <- slice (numBinOp Add tX tY) sliceConfig
  rhs <- numBinOp Add (slice tX sliceConfig) (slice tY sliceConfig)
  rewrite "Slice(Add(X, Y), S, E, P) ==> Add(Slice(X, S, E, P), Slice(Y, S, E, P))" lhs rhs

main :: IO ()
main = do
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule02_v1 ##############################"
  verifyNumDSL rule02_v1
  print "############################## rule02_v2 ##############################"
  verifyNumDSL rule02_v2
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule03_v1 ##############################"
  verifyNumDSL rule03_v1
  print "############################## rule03_not_ge ##############################"
  verifyNumDSL rule03_not_ge
  print "############################## rule03_not_le ##############################"
  verifyNumDSL rule03_not_le
  print "############################## rule03_not_eq ##############################"
  verifyNumDSL rule03_not_eq
  print "############################## rule03_not_ne ##############################"
  verifyNumDSL rule03_not_ne
  print "############################## rule03_not_gt ##############################"
  verifyNumDSL rule03_not_gt
  print "############################## rule03_not_lt ##############################"
  verifyNumDSL rule03_not_lt
  print "############################## rule03_and_not ##############################"
  verifyDSL rule03_and_not
  print "############################## rule03_or_not ##############################"
  verifyDSL rule03_or_not
  print "############################## rule03_and ##############################"
  verifyDSL rule03_and
  print "############################## rule03_or ##############################"
  verifyDSL rule03_or
  print "############################## rule04 ##############################"
  verifyDSL rule04
  print "############################## rule04_v1 ##############################"
  verifyDSL rule04_v1
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule05_v1 ##############################"
  verifyNumDSL rule05_v1
  print "############################## rule05_v2 ##############################"
  verifyNumDSL rule05_v2
  print "############################## rule05_v3 ##############################"
  verifyNumDSL rule05_v3
  print "############################## rule05_v4 ##############################"
  verifyNumDSL rule05_v4
  print "############################## rule06_forward ##############################"
  verifyNumDSL rule06_forward
  print "############################## rule06_backward ##############################"
  verifyNumDSL rule06_backward
  print "############################## rule08 ##############################"
  verifyNumDSL rule08
  print "############################## rule09_forward ##############################"
  verifyNumDSL rule09_forward
  print "############################## rule09_backward ##############################"
  verifyNumDSL rule09_backward
  print "############################## rule09_slice_forward ##############################"
  verifyNumDSL rule09_slice_forward
  print "############################## rule09_slice_backward ##############################"
  verifyNumDSL rule09_slice_backward
