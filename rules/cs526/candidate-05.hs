module Main (main) where

import Grisette hiding (dot, (-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  [xs0, ys0, dotsi, sixc, siyd, sir, rclass0AllOne] <-
    newMaps
      ["xs0", "ys0", "dotsi", "sixc", "siyd", "sir", "allOne"]
      rclass0
  [xs1, ys1] <- newMaps ["xs1", "ys1"] rclass1
  [cs2, ds2] <- newMaps ["cs2", "ds2"] rclass2
  x <- newTensor @a "x" [rclass0 --> xs0, rclass1 --> xs1]
  y <- newTensor @a "y" [rclass0 --> ys0, rclass1 --> ys1]
  c <- newTensor @a "c" [rclass0 --> xs0, rclass2 --> cs2]
  d <- newTensor @a "d" [rclass0 --> ys0, rclass2 --> ds2]
  lhs <-
    dot
      (concatTensor x y $ ByRClass rclass0)
      (concatTensor c d $ ByRClass rclass0)
      [rclass0 --> dotsi]
      []
  rhs <-
    reduce
      ( concatTensor
          (broadcast (dot x c [rclass0 --> sixc] []) [rclass0 --> rclass0AllOne])
          (broadcast (dot y d [rclass0 --> siyd] []) [rclass0 --> rclass0AllOne])
          $ ByRClass rclass0
      )
      [rclass0 --> sir]
  precondition [rclass0AllOne] $ \[rclass0AllOne] -> rclass0AllOne .== 1
  let siCondition [vdotsi, vsixc, vsiyd, vsir, vxs0, vys0] =
        symIte
          (vsir .== 0)
          (vdotsi .== vsixc)
          (vdotsi .== vsiyd + vxs0)
          .&& (vsixc .>= 0)
          .&& (vsiyd .>= 0)
          .&& (vsixc .< vxs0)
          .&& (vsiyd .< vys0)
          .&& (vsir .== 0 .|| vsir .== 1)
      siCondition _ = undefined
  siRelation [dotsi, sixc, siyd, sir, xs0, ys0] siCondition
  checkSIMap [dotsi] [sir, sixc, siyd]
  let lhsStr = "Dot(Concat(X, Y), Concat(C, D))"
  let rhsStr = "Reduce(Concat(Broadcast(Dot(X, C)), Broadcast(Dot(Y, D)))"
  rewrite (lhsStr <> " ⇒ " <> rhsStr) lhs rhs

rule02_forward :: forall a. NumRule a
rule02_forward _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0sizeXY, rc0sizeUV] <- newMaps ["rc0sizeX", "rc0sizeUV"] rclass0
  rc1size <- newMap "rc1size" rclass1
  zeroMap <- newConstMap "zeroMap" 0 rclass0
  oneMap <- newConstMap "oneMap" 1 rclass0
  tX <- newTensor @a "X" [rclass0 --> rc0sizeXY, rclass1 --> rc1size]
  tY <- newTensor @a "Y" [rclass0 --> rc0sizeXY, rclass1 --> rc1size]
  tU <- newTensor @a "U" [rclass0 --> rc0sizeUV, rclass1 --> rc1size]
  tV <- newTensor @a "V" [rclass0 --> rc0sizeUV, rclass1 --> rc1size]
  lhs <- concatTensor (numBinOp Mul tX tY) (numBinOp Mul tU tV) (ByRClass rclass0)
  rhs <- numBinOp Mul (concatTensor tX tU (ByRClass rclass0)) (concatTensor tY tV (ByRClass rclass0))
  rewrite "Concat(Mul(X, Y), Mul(U, V), dim) ==> Mul(Concat(X, U, dim), Concat(Y, V, dim))" lhs rhs

rule02_backward :: forall a. NumRule a
rule02_backward _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0sizeXY, rc0sizeUV] <- newMaps ["rc0sizeX", "rc0sizeUV"] rclass0
  rc1size <- newMap "rc1size" rclass1
  zeroMap <- newConstMap "zeroMap" 0 rclass0
  oneMap <- newConstMap "oneMap" 1 rclass0
  tX <- newTensor @a "X" [rclass0 --> rc0sizeXY, rclass1 --> rc1size]
  tY <- newTensor @a "Y" [rclass0 --> rc0sizeXY, rclass1 --> rc1size]
  tU <- newTensor @a "U" [rclass0 --> rc0sizeUV, rclass1 --> rc1size]
  tV <- newTensor @a "V" [rclass0 --> rc0sizeUV, rclass1 --> rc1size]
  lhs <- numBinOp Mul (concatTensor tX tU (ByRClass rclass0)) (concatTensor tY tV (ByRClass rclass0))
  rhs <- concatTensor (numBinOp Mul tX tY) (numBinOp Mul tU tV) (ByRClass rclass0)
  rewrite "Mul(Concat(X, U, dim), Concat(Y, V, dim)) ==> Concat(Mul(X, Y), Mul(U, V), dim)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02_forward ##############################"
  verifyNumDSL rule02_forward
  print "############################## rule02_backward ##############################"
  verifyNumDSL rule02_backward
