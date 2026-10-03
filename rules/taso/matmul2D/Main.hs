module Main (main) where

import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (checkSIMap, siRelation)
import TensorRight.Internal.DSL.TASO (concat, ewadd, matmul2D, smul, transpose)
import Prelude hiding (concat)

-- TASO's verified rewrite language defines matmul only for rank-two tensors.
-- 'matmul2D' records those rank conditions; the remaining constraints are
-- asserted by the existing dot backend.

matmulAssociativity :: forall a. NumRule a
matmulAssociativity _ = do
  [m, k, n, p] <- newRClasses ["m", "k", "n", "p"]
  mSize <- newMap "mSize" m
  kSize <- newMap "kSize" k
  nSize <- newMap "nSize" n
  pSize <- newMap "pSize" p
  x <- newTensor @a "x" [m --> mSize, k --> kSize]
  y <- newTensor @a "y" [k --> kSize, n --> nSize]
  z <- newTensor @a "z" [n --> nSize, p --> pSize]
  kL <- newMap "kL" k
  kR <- newMap "kR" k
  nL <- newMap "nL" n
  nR <- newMap "nR" n
  siRelation [kL, kR] $ \[l, r] -> l .== r
  siRelation [nL, nR] $ \[l, r] -> l .== r
  checkSIMap [kL, nL] [kR, nR]
  lhs <- matmul2D x (matmul2D y z [n --> nL]) [k --> kL]
  rhs <- matmul2D (matmul2D x y [k --> kR]) z [n --> nR]
  rewrite "matmul(x, matmul(y, z)) => matmul(matmul(x, y), z)" lhs rhs

matmulScalarLinear :: forall a. NumRule a
matmulScalarLinear _ = do
  [m, k, n] <- newRClasses ["m", "k", "n"]
  mSize <- newMap "mSize" m
  kSize <- newMap "kSize" k
  nSize <- newMap "nSize" n
  x <- newTensor @a "x" [m --> mSize, k --> kSize]
  y <- newTensor @a "y" [k --> kSize, n --> nSize]
  kL <- newMap "kL" k
  kR <- newMap "kR" k
  siRelation [kL, kR] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR]
  lhs <- smul (matmul2D x y [k --> kL]) ("w" :: a)
  rhs <- matmul2D x (smul y ("w" :: a)) [k --> kR]
  rewrite "smul(matmul(x, y), w) => matmul(x, smul(y, w))" lhs rhs

-- Implemented for the TASO checklist but unsupported by the current backend;
-- see the note before 'matmulMixedConcat'.
matmulRightAddition :: forall a. NumRule a
matmulRightAddition _ = do
  [m, k, n] <- newRClasses ["m", "k", "n"]
  mSize <- newMap "mSize" m
  kSize <- newMap "kSize" k
  nSize <- newMap "nSize" n
  x <- newTensor @a "x" [m --> mSize, k --> kSize]
  y <- newTensor @a "y" [k --> kSize, n --> nSize]
  z <- newTensor @a "z" [k --> kSize, n --> nSize]
  kL <- newMap "kL" k
  kR1 <- newMap "kR1" k
  kR2 <- newMap "kR2" k
  siRelation [kL, kR1] $ \[l, r] -> l .== r
  siRelation [kL, kR2] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR1, kR2]
  lhs <- matmul2D x (ewadd y z) [k --> kL]
  rhs <- ewadd (matmul2D x y [k --> kR1]) (matmul2D x z [k --> kR2])
  rewrite "matmul(x, ewadd(y, z)) => ewadd(matmul(x, y), matmul(x, z))" lhs rhs

matmulTranspose :: forall a. NumRule a
matmulTranspose _ = do
  [m, k, n] <- newRClasses ["m", "k", "n"]
  mSize <- newMap "mSize" m
  kSize <- newMap "kSize" k
  nSize <- newMap "nSize" n
  x <- newTensor @a "x" [m --> mSize @@ "L", k --> kSize @@ "K"]
  y <- newTensor @a "y" [k --> kSize @@ "K", n --> nSize @@ "R"]
  kL <- newMap "kL" k
  kR <- newMap "kR" k
  siRelation [kL, kR] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR]
  lhs <- transpose =<< matmul2D x y [ByLabel "K" --> kL]
  yt <- transpose y
  xt0 <- transpose x
  xt <- relabel xt0 [ByLabel "L" --> ByLabel "R", ByLabel "K" --> ByLabel "K'"]
  rhs0 <- matmul2D yt xt [ByLabel "R" --> kR]
  rhs <- relabel rhs0 [ByLabel "K'" --> ByLabel "R", ByLabel "K" --> ByLabel "L"]
  rewrite "transpose(matmul(x, y)) => matmul(transpose(y), transpose(x))" lhs rhs

matmulRightConcat :: forall a. NumRule a
matmulRightConcat _ = do
  [m, k, n] <- newRClasses ["m", "k", "n"]
  mSize <- newMap "mSize" m
  kSize <- newMap "kSize" k
  [n1Size, n2Size] <- newMaps ["n1Size", "n2Size"] n
  x <- newTensor @a "x" [m --> mSize, k --> kSize]
  y <- newTensor @a "y" [k --> kSize, n --> n1Size]
  z <- newTensor @a "z" [k --> kSize, n --> n2Size]
  kL1 <- newMap "kL1" k
  kL2 <- newMap "kL2" k
  kR <- newMap "kR" k
  siRelation [kL1, kR] $ \[l, r] -> l .== r
  siRelation [kL2, kR] $ \[l, r] -> l .== r
  checkSIMap [kL1, kL2] [kR]
  xy <- matmul2D x y [k --> kL1]
  xz <- matmul2D x z [k --> kL2]
  lhs <- concat (ByRClass n) xy xz
  yz <- concat (ByRClass n) y z
  rhs <- matmul2D x yz [k --> kR]
  rewrite "concat(1, matmul(x, y), matmul(x, z)) => matmul(x, concat(1, y, z))" lhs rhs

-- The upstream right-addition and block-concatenation axioms are intentionally
-- not in this executable yet. Both use 'ewadd' on independent dot reductions;
-- a 'TensorElemSum' is a reduction binder rather than an ordinary value, so
-- pointwise addition of two such elements is not a sound backend operation.
--
-- The block-concatenation axiom additionally has a partitioned contraction
-- correspondence: its concatenated contraction domain must correspond
-- piecewise to two independent RHS reduction domains. The current SI relation
-- mechanism relates one selected index from each dot and cannot express that
-- partition without making an RHS access out of range.
--
-- The XLA Dot(Concat(...), Concat(...)) rule handles its analogous equation by
-- encoding the RHS as Reduce(Concat(Broadcast(Dot(...)), Broadcast(Dot(...))));
-- the extra reduction supplies a selector for the two branches. TASO states
-- the result directly as an elementwise addition, so that selector is absent
-- here. Keep the source-faithful rules below for the checklist, but do not
-- invoke them from 'main' until the backend and SI relation model support them.
--
matmulMixedConcat :: forall a. NumRule a
matmulMixedConcat _ = do
  [m, k, n] <- newRClasses ["m", "k", "n"]
  mSize <- newMap "mSize" m
  [k1Size, k2Size] <- newMaps ["k1Size", "k2Size"] k
  nSize <- newMap "nSize" n
  x <- newTensor @a "x" [m --> mSize, k --> k1Size]
  y <- newTensor @a "y" [k --> k1Size, n --> nSize]
  z <- newTensor @a "z" [m --> mSize, k --> k2Size]
  w <- newTensor @a "w" [k --> k2Size, n --> nSize]
  kL <- newMap "kL" k
  kR1 <- newMap "kR1" k
  kR2 <- newMap "kR2" k
  siRelation [kL, kR1] $ \[l, r] -> l .== r
  siRelation [kL, kR2] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR1, kR2]
  xz <- concat (ByRClass k) x z
  yw <- concat (ByRClass k) y w
  lhs <- matmul2D xz yw [k --> kL]
  rhs <- ewadd (matmul2D x y [k --> kR1]) (matmul2D z w [k --> kR2])
  rewrite "matmul(concat(1, x, z), concat(0, y, w)) => ewadd(matmul(x, y), matmul(z, w))" lhs rhs

main :: IO ()
main = do
  verifyNumDSL matmulAssociativity
  verifyNumDSL matmulScalarLinear
  verifyNumDSL matmulTranspose
  verifyNumDSL matmulRightConcat
