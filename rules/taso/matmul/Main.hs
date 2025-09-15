module Main (main) where

import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (checkSIMap, siRelation)
import TensorRight.Internal.DSL.TASO (concat, ewadd, ewmul, matmul2D, relu, smul, transpose)
import Prelude hiding (concat)

-- | Rule 1: Matrix multiplication associativity
-- ∀x, y, z. matmul(x, matmul(y, z)) = matmul(matmul(x, y), z)
matmulAssociativity :: forall a. NumRule a
matmulAssociativity _ = do
  [rclassM, rclassK, rclassN, rclassP] <- newRClasses ["rclassM", "rclassK", "rclassN", "rclassP"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN
  sizeP <- newMap "sizeP" rclassP

  x <- newTensor @a "x" [rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassK --> sizeK, rclassN --> sizeN] -- Shared K and N
  z <- newTensor @a "z" [rclassN --> sizeN, rclassP --> sizeP] -- Shared N
  (yzExpr, nL) <- matmul2D y z
  (xyExpr, kR) <- matmul2D x y

  (lhs, kL) <- matmul2D x yzExpr
  (rhs, nR) <- matmul2D xyExpr z

  siRelation [kL, kR] $ \[l, r] -> l .== r
  siRelation [nL, nR] $ \[l, r] -> l .== r
  checkSIMap [kL, nL] [kR, nR]

  rewrite "matmul(x, matmul(y, z)) ⇒ matmul(matmul(x, y), z)" lhs rhs

-- | Rule 2: Matrix multiplication is linear (scalar multiplication)
-- ∀x, y, w. smul(matmul(x, y), w) = matmul(x, smul(y, w))
matmulScalarLinear :: forall a. NumRule a
matmulScalarLinear _ = do
  let w = ("w" :: a)
  [rclassM, rclassK, rclassN] <- newRClasses ["rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassK --> sizeK, rclassN --> sizeN]

  (xy, kL) <- matmul2D x y
  lhs <- smul xy w
  yw <- smul y w
  (rhs, kR) <- matmul2D x yw

  siRelation [kL, kR] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR]

  rewrite "smul(matmul(x, y), w) ⇒ matmul(x, smul(y, w))" lhs rhs

-- | Rule 3: Matrix multiplication distributes over addition
-- ∀x, y, z. matmul(x, ewadd(y, z)) = ewadd(matmul(x, y), matmul(x, z))
matmulDistributive :: forall a. NumRule a
matmulDistributive _ = do
  [rclassM, rclassK, rclassN] <- newRClasses ["rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassK --> sizeK, rclassN --> sizeN]
  z <- newTensor @a "z" [rclassK --> sizeK, rclassN --> sizeN]

  yz <- ewadd y z
  (lhs, kL) <- matmul2D x yz
  (xy, kR1) <- matmul2D x y
  (xz, kR2) <- matmul2D x z
  rhs <- ewadd xy xz

  siRelation [kL, kR1] $ \[l, r] -> l .== r
  siRelation [kL, kR2] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR1, kR2]

  rewrite "matmul(x, ewadd(y, z)) ⇒ ewadd(matmul(x, y), matmul(x, z))" lhs rhs

-- | Rule 4: Matrix multiplication and transpose interaction
-- ∀x, y. transpose(matmul(x, y)) = matmul(transpose(y), transpose(x))
matmulTranspose :: forall a. NumRule a
matmulTranspose _ = do
  [rclassM, rclassK, rclassN] <- newRClasses ["rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN

  -- Label axes so transpose works via label swap instead of ByRClass swap
  x <- newTensor @a "x" [rclassM --> sizeM @@ "L", rclassK --> sizeK @@ "K"]
  y <- newTensor @a "y" [rclassK --> sizeK @@ "K", rclassN --> sizeN @@ "R"]
  (xy, kL) <- matmul2D x y -- TODO: Pass the rclass explicitly instead of inferring
  lhs <- transpose xy
  yt <- transpose y
  xt <- transpose x
  (rhs, kR) <- matmul2D yt xt

  siRelation [kL, kR] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR]

  rewrite "transpose(matmul(x, y)) ⇒ matmul(transpose(y), transpose(x))" lhs rhs

-- | Rule 5: Identity matrix property
-- ∀x. matmul(x, I) = x (where I is identity matrix)
matmulIdentity :: forall a. NumRule a
matmulIdentity _ = do
  [rclassM, rclassN] <- newRClasses ["rclassM", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM, rclassN --> sizeN]
  identityRow <- iota [rclassM --> sizeM, rclassN --> sizeN] (ByRClass rclassM)
  identityCol <- iota [rclassM --> sizeM, rclassN --> sizeN] (ByRClass rclassN)
  identityMask <- compareOp Eqv identityRow identityCol
  ones <- constant @a 1 [rclassM --> sizeM, rclassN --> sizeN]
  zeros <- constant @a 0 [rclassM --> sizeM, rclassN --> sizeN]
  identityMatrix <- select identityMask ones zeros

  -- Precondition: matrix must be square
  precondition [sizeM, sizeN] $ \[m, n] -> m .== n

  (lhs, _) <- matmul2D x identityMatrix
  let rhs = x

  monitorExprOnFailure "x" x
  monitorExprOnFailure "I" identityMatrix

  rewrite "matmul(x, I) ⇒ x" lhs rhs

-- -- | Rule 6: Concatenation and matrix multiplication (right distributive)
-- -- ∀x, y, z. concat(1, matmul(x, y), matmul(x, z)) = matmul(x, concat(1, y, z))
matmulConcatRight :: forall a. NumRule a
matmulConcatRight _ = do
  [rclassM, rclassK, rclassN] <- newRClasses ["rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  [sizeN1, sizeN2] <- newMaps ["sizeN1", "sizeN2"] rclassN

  x <- newTensor @a "x" [rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassK --> sizeK, rclassN --> sizeN1]
  z <- newTensor @a "z" [rclassK --> sizeK, rclassN --> sizeN2]

  (xy, kL1) <- matmul2D x y
  (xz, kL2) <- matmul2D x z
  lhs <- concat (ByRClass rclassN) xy xz
  yz <- concat (ByRClass rclassN) y z
  (rhs, kR) <- matmul2D x yz

  siRelation [kL1, kR] $ \[l, r] -> l .== r
  siRelation [kL2, kR] $ \[l, r] -> l .== r
  checkSIMap [kL1, kL2] [kR]

  rewrite "concat(1, matmul(x, y), matmul(x, z)) ⇒ matmul(x, concat(1, y, z))" lhs rhs

-- | Rule 7: Concatenation and matrix multiplication (mixed)
-- ∀x, y, z, w. matmul(concat(1, x, z), concat(0, y, w)) = ewadd(matmul(x, y), matmul(z, w))
matmulConcatMixed :: forall a. NumRule a
matmulConcatMixed _ = do
  [rclassM, rclassK, rclassN] <- newRClasses ["rclassM", "rclassK", "rclassN"]
  [sizeM1, sizeM2] <- newMaps ["sizeM1", "sizeM2"] rclassM
  [sizeK1, sizeK2] <- newMaps ["sizeK1", "sizeK2"] rclassK
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM1, rclassK --> sizeK1]
  y <- newTensor @a "y" [rclassK --> sizeK1, rclassN --> sizeN]
  z <- newTensor @a "z" [rclassM --> sizeM2, rclassK --> sizeK2]
  w <- newTensor @a "w" [rclassK --> sizeK2, rclassN --> sizeN]

  -- Dimensions must match appropriately for concatenation and matmul
  precondition [sizeM1, sizeM2] $ \[m1, m2] -> m1 .== m2
  precondition [sizeK1, sizeK2] $ \[k1, k2] -> k1 .== k2

  xz <- concat (ByRClass rclassM) x z
  yw <- concat (ByRClass rclassK) y w
  (lhs, kL) <- matmul2D xz yw
  (xy, kR1) <- matmul2D x y
  (zw, kR2) <- matmul2D z w
  rhs <- ewadd xy zw

  siRelation [kL, kR1] $ \[l, r] -> l .== r
  siRelation [kL, kR2] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR1, kR2]

  rewrite "matmul(concat(1, x, z), concat(0, y, w)) ⇒ ewadd(matmul(x, y), matmul(z, w))" lhs rhs

main :: IO ()
main = do
  printTitle "#################### matmulAssociativity ####################"
  verifyNumDSL matmulAssociativity
  printTitle "#################### matmulScalarLinear #####################"
  verifyNumDSL matmulScalarLinear
  printTitle "#################### matmulDistributive #####################"
  verifyNumDSL matmulDistributive

-- printTitle "###################### matmulTranspose ######################"
-- verifyNumDSL matmulTranspose

-- printTitle "###################### matmulIdentity #######################"
-- verifyNumDSL matmulIdentity

-- printTitle "#################### matmulConcatRight ######################"
-- verifyNumDSL matmulConcatRight
-- printTitle "##################### matmulConcatMixed #####################"
-- verifyNumDSL matmulConcatMixed
