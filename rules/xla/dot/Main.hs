module Main (main) where

import Debug.Trace (traceShow)
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

rule02 :: forall a. NumRule a
rule02 _ = do
  [rclass0, rclass1, rclass2, rclass3] <- newRClasses ["rclass0", "rclass1", "rclass2", "rclass3"]
  [size0, lhssi0, rhssi0] <- newMaps ["size0", "lhssi0", "rhssi0"] rclass0
  size1 <- newMap "size1" rclass1
  size2 <- newMap "size2" rclass2
  size3 <- newMap "size3" rclass3
  a <- newTensor @a "a" [rclass0 --> size0, rclass1 --> size1, rclass2 --> size2]
  b <- newTensor @a "b" [rclass0 --> size0, rclass1 --> size1, rclass3 --> size3]
  lhs <- dot a b [rclass0 --> lhssi0] [ByRClass rclass1]
  rhs <- dot b a [rclass0 --> rhssi0] [ByRClass rclass1]
  siRelation [lhssi0, rhssi0] $ \[vlhssi0, vrhssi0] -> vlhssi0 .== vrhssi0
  checkSIMap [lhssi0] [rhssi0]
  rewrite "Dot(A, B) ⇒ Dot(B, A)" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  [rclass0, rclass1, rclass2, rclass3] <- newRClasses ["rclass0", "rclass1", "rclass2", "rclass3"]
  [sizea0] <- newMaps ["sizea0"] rclass0
  [sizea1, sizeb1, siabLhs, siabRhs] <- newMaps ["sizea1", "sizeb1", "siabLhs", "siabRhs"] rclass1
  [sizeb2, sizec2, sibcLhs, sibcRhs] <- newMaps ["sizeb2", "sizec2", "sibcLhs", "sibcRhs"] rclass2
  [sizec3] <- newMaps ["sizec3"] rclass3

  tensorA <- newTensor @a "tensorA" [rclass0 --> sizea0, rclass1 --> sizea1]
  tensorB <- newTensor @a "tensorB" [rclass1 --> sizeb1, rclass2 --> sizeb2]
  tensorC <- newTensor @a "tensorC" [rclass2 --> sizec2, rclass3 --> sizec3]

  lhs <-
    dot
      tensorA
      ( dot
          tensorB
          tensorC
          [rclass2 --> sibcLhs]
          []
      )
      [rclass1 --> siabLhs]
      []
  rhs <-
    dot
      ( dot
          tensorA
          tensorB
          [rclass1 --> siabRhs]
          []
      )
      tensorC
      [rclass2 --> sibcRhs]
      []

  siRelation [siabLhs, siabRhs] $ \[vsiabLhs, vsiabRhs] -> vsiabLhs .== vsiabRhs
  siRelation [sibcLhs, sibcRhs] $ \[vsibcLhs, vsibcRhs] -> vsibcLhs .== vsibcRhs
  checkSIMap [siabLhs, sibcLhs] [siabRhs, sibcRhs]

  rewrite "Dot(A,Dot(B,C)) ⇒ Dot(Dot(A,B),C)" lhs lhs

rule04 :: forall a. NumRule a
rule04 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  rclass0Size <- newMap "rclass0Size" rclass0
  rclass1Size <- newMap "rclass1Size" rclass1
  rclass2Size <- newMap "rclass2Size" rclass2
  x <- newTensor @a "x" [rclass0 --> rclass0Size, rclass1 --> rclass1Size]
  y <- newTensor @a "y" [rclass0 --> rclass0Size, rclass2 --> rclass2Size]
  lhs <- dot x y [] [ByRClass rclass0]
  rhs <-
    numBinOp
      Mul
      (broadcast x [rclass2 --> rclass2Size])
      (broadcast y [rclass1 --> rclass1Size])
  rewrite "Dot(A,B) ⇒ Mul(Broadcast(A), Broadcast(B)) when no contraction" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  [rclass0, rclass1, crclass0, crclass1, brclass0, brclass1] <-
    newRClasses ["rclass0", "rclass1", "crclass0", "crclass1", "brclass0", "brclass1"]
  rclass0Size <- newMap "rclass0Size" rclass0
  rclass1Size <- newMap "rclass1Size" rclass1
  crclass0Size <- newMap "crclass0Size" crclass0
  crclass1Size <- newMap "crclass1Size" crclass1
  brclass0Size <- newMap "brclassSize" brclass0
  brclass1Size <- newMap "brclassSize" brclass1
  si0 <- newMap "si0" crclass0
  si1 <- newMap "si1" crclass1
  x <-
    newTensor @a
      "x"
      [ rclass0 --> rclass0Size,
        crclass0 --> crclass0Size,
        crclass1 --> crclass1Size,
        brclass0 --> brclass0Size,
        brclass1 --> brclass1Size
      ]
  y <-
    newTensor @a
      "y"
      [ rclass1 --> rclass1Size,
        crclass0 --> crclass0Size,
        crclass1 --> crclass1Size,
        brclass0 --> brclass0Size,
        brclass1 --> brclass1Size
      ]
  lhs <- dot x y [crclass0 --> si0, crclass1 --> si1] [ByRClass brclass0, ByRClass brclass1]
  rhs <-
    constant @a
      0
      [ rclass0 --> rclass0Size,
        rclass1 --> rclass1Size,
        brclass0 --> brclass0Size,
        brclass1 --> brclass1Size
      ]
  precondition'
    [ rclass0Size,
      rclass1Size,
      crclass0Size,
      crclass1Size,
      brclass0Size,
      brclass1Size
    ]
    $ \[rclass0Size, rclass1Size, crclass0Size, crclass1Size, brclass0Size, brclass1Size] ->
      zipCondition (\[rclass0Size] -> rclass0Size .== 0) [rclass0Size]
        .|| zipCondition (\[rclass1Size] -> rclass1Size .== 0) [rclass1Size]
        .|| zipCondition (\[crclassSize] -> crclassSize .== 0) [crclass0Size]
        .|| zipCondition (\[crclassSize] -> crclassSize .== 0) [crclass1Size]
        .|| zipCondition (\[brclassSize] -> brclassSize .== 0) [brclass0Size]
        .|| zipCondition (\[brclassSize] -> brclassSize .== 0) [brclass1Size]
  rewrite "Dot(A,B) ⇒ 0 when one of the dimensions is 0" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  [rclass, crclass, brclass] <- newRClasses ["rclass", "crclass", "brclass"]
  rclassSize <- newMap "rclassSize" rclass
  crclassSize <- newMap "crclassSize" crclass
  brclassSize <- newMap "brclassSize" brclass
  x <- newTensor @a "x" [rclass --> rclassSize, crclass --> crclassSize, brclass --> brclassSize]
  y <- newTensor @a "y" [crclass --> crclassSize, brclass --> brclassSize]
  si <- newMap "si" crclass
  rsi <- newMap "rsi" crclass
  lhs <- dot x y [crclass --> si] [ByRClass brclass]
  rhs <-
    reduce
      ( numBinOp
          Mul
          x
          (broadcast y [rclass --> rclassSize])
      )
      [crclass --> rsi]
  siRelation [si, rsi] $ \[vsi, vrsi] -> vsi .== vrsi
  checkSIMap [si] [rsi]
  rewrite
    ( "Dot(A,B) ⇒ Reduce(Mul(Broadcast(Transpose(A)), Broadcast(Transpose(B)))) "
        <> "when rhs only have contraction and batch rclasses"
    )
    lhs
    rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSLWith cvc5 rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule06 ##############################"
  verifyNumDSL rule06
