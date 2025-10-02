module Main (main) where

import Debug.Trace
import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (checkSIMap, monitorExprOnFailure, newSingletonRClass, newSingletonRClasses, siRelation)
import TensorRight.Internal.DSL.TASO (concat, ewadd, ewmul, matmul2D, relu, smul, transpose)
import Prelude hiding (concat)

-- | Rule 1: Matrix multiplication associativity
-- ∀x, y, z. matmul(x, matmul(y, z)) = matmul(matmul(x, y), z)
matmulAssociativity :: forall a. NumRule a
matmulAssociativity _ = do
  [rclassM, rclassK, rclassN, rclassP] <- newSingletonRClasses ["rclassM", "rclassK", "rclassN", "rclassP"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN
  sizeP <- newMap "sizeP" rclassP

  x <- newTensor @a "x" [rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassK --> sizeK, rclassN --> sizeN] -- Shared K and N
  z <- newTensor @a "z" [rclassN --> sizeN, rclassP --> sizeP] -- Shared N
  nL <- newMap "contractSI" rclassN
  nR <- newMap "contractSI" rclassN

  kL <- newMap "contractSI" rclassK
  kR <- newMap "contractSI" rclassK

  siRelation [kL, kR] $ \[l, r] -> l .== r
  siRelation [nL, nR] $ \[l, r] -> l .== r
  checkSIMap [kL, nL] [kR, nR]

  lhs <- matmul2D x (matmul2D y z [rclassN --> nL]) [rclassK --> kL]
  rhs <- matmul2D (matmul2D x y [rclassK --> kR]) z [rclassN --> nR]

  rewrite "matmul(x, matmul(y, z)) ⇒ matmul(matmul(x, y), z)" lhs rhs

-- | Rule 2: Matrix multiplication is linear (scalar multiplication)
-- ∀x, y, w. smul(matmul(x, y), w) = matmul(x, smul(y, w))
matmulScalarLinear :: forall a. NumRule a
matmulScalarLinear _ = do
  let w = ("w" :: a)
  [rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassK --> sizeK, rclassN --> sizeN]

  kL <- newMap "contractSI" rclassK
  kR <- newMap "contractSI" rclassK
  xy <- matmul2D x y [rclassK --> kL]
  lhs <- smul xy w
  yw <- smul y w
  rhs <- matmul2D x yw [rclassK --> kR]

  siRelation [kL, kR] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR]

  rewrite "smul(matmul(x, y), w) ⇒ matmul(x, smul(y, w))" lhs rhs

-- | Rule 3: Matrix multiplication distributes over addition
-- ∀x, y, z. matmul(x, ewadd(y, z)) = ewadd(matmul(x, y), matmul(x, z))
matmulDistributive :: forall a. NumRule a
matmulDistributive _ = do
  [rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassK --> sizeK, rclassN --> sizeN]
  z <- newTensor @a "z" [rclassK --> sizeK, rclassN --> sizeN]

  yz <- ewadd y z
  kL <- newMap "contractSI" rclassK
  kR1 <- newMap "contractSI" rclassK
  kR2 <- newMap "contractSI" rclassK
  lhs <- matmul2D x yz [rclassK --> kL]
  xy <- matmul2D x y [rclassK --> kR1]
  xz <- matmul2D x z [rclassK --> kR2]
  rhs <- ewadd xy xz

  siRelation [kL, kR1] $ \[l, r] -> l .== r
  siRelation [kL, kR2] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR1, kR2]

  rewrite "matmul(x, ewadd(y, z)) ⇒ ewadd(matmul(x, y), matmul(x, z))" lhs rhs

-- | Rule 4: Matrix multiplication and transpose interaction
-- ∀x, y. transpose(matmul(x, y)) = matmul(transpose(y), transpose(x))
matmulTranspose :: forall a. NumRule a
matmulTranspose _ = do
  [rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN

  -- Labelled inputs
  x <- newTensor @a "x" [rclassM --> sizeM @@ "L", rclassK --> sizeK @@ "K"]
  y <- newTensor @a "y" [rclassK --> sizeK @@ "K", rclassN --> sizeN @@ "R"]

  -- LHS: transpose(matmul(x, y))
  kL <- newMap "contractSI" rclassK
  -- xy should be [rclassM @@ "L" rclassN @@ "R"]
  xy <- matmul2D x y [ByLabel "K" --> kL]
  -- lhs should be [rclassM @@ "R" rclassN @@ "L"]
  lhs <- transpose xy

  -- RHS: matmul(transpose(y), transpose(x))
  yt <- transpose y -- [rclassK @@ "R", rclassN @@ "K"]
  xt0 <- transpose x -- [rclassM @@ "K", rclassK @@ "L"]
  xt <- relabel xt0 [ByLabel "L" --> ByLabel "R", ByLabel "K" --> ByLabel "K'"] -- [rclassM @@ "K'", rclassK @@ "R"]
  kR <- newMap "contractSI" rclassK
  rhs0 <- matmul2D yt xt [ByLabel "R" --> kR] -- [rclassN @@ "K", rclassM @@ "K'"]
  -- rhs should now also be [rclassM @@ "R" rclassN @@ "L"]
  rhs <- relabel rhs0 [ByLabel "K'" --> ByLabel "R", ByLabel "K" --> ByLabel "L"]

  siRelation [kL, kR] $ \[i, j] -> i .== j
  checkSIMap [kL] [kR]

  rewrite "transpose(matmul(x, y)) ⇒ matmul(transpose(y), transpose(x))" lhs rhs

-- | Rule 5: Identity matrix property
-- ∀x. matmul(x, I) = x (where I is identity matrix)
matmulIdentity :: forall a. NumRule a
matmulIdentity _ = do
  [rclassM, rclassN] <- newSingletonRClasses ["rclassM", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM, rclassN --> sizeN @@ "L"]
  identityRow <- iota [rclassN --> sizeN @@ "L", rclassN --> sizeN @@ "R"] (ByLabel "L")
  identityCol <- iota [rclassN --> sizeN @@ "L", rclassN --> sizeN @@ "R"] (ByLabel "R")
  identityMask <- compareOp Eqv identityRow identityCol
  ones <- constant @a 1 [rclassN --> sizeN @@ "L", rclassN --> sizeN @@ "R"]
  zeros <- constant @a 0 [rclassN --> sizeN @@ "L", rclassN --> sizeN @@ "R"]
  identityMatrix <- select identityMask ones zeros

  nL <- newMap "contractSI" rclassN
  -- lhs should be [rclassM, rclassN @@ "R"]
  lhs <- matmul2D x identityMatrix [ByLabel "L" --> nL]
  rhs <- relabel x [ByLabel "L" --> ByLabel "R"]

  siRelation [sizeN] $ \[i, j] -> i .== j
  checkSIMap [sizeN] [nL]

  rewrite "matmul(x, I) ⇒ x" lhs rhs

-- -- | Rule 6: Concatenation and matrix multiplication (right distributive)
-- -- ∀x, y, z. concat(1, matmul(x, y), matmul(x, z)) = matmul(x, concat(1, y, z))
matmulConcatRight :: forall a. NumRule a
matmulConcatRight _ = do
  [rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  [sizeN1, sizeN2] <- newMaps ["sizeN1", "sizeN2"] rclassN

  x <- newTensor @a "x" [rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassK --> sizeK, rclassN --> sizeN1]
  z <- newTensor @a "z" [rclassK --> sizeK, rclassN --> sizeN2]

  kL1 <- newMap "contractSI" rclassK
  kL2 <- newMap "contractSI" rclassK
  xy <- matmul2D x y [rclassK --> kL1]
  xz <- matmul2D x z [rclassK --> kL2]
  lhs <- concat (ByRClass rclassN) xy xz
  yz <- concat (ByRClass rclassN) y z
  kR <- newMap "contractSI" rclassK
  rhs <- matmul2D x yz [rclassK --> kR]

  siRelation [kL1, kR] $ \[l, r] -> l .== r
  siRelation [kL2, kR] $ \[l, r] -> l .== r
  checkSIMap [kL1, kL2] [kR]

  rewrite "concat(1, matmul(x, y), matmul(x, z)) ⇒ matmul(x, concat(1, y, z))" lhs rhs

-- | Rule 7: Concatenation and matrix multiplication (mixed)
-- ∀x, y, z, w. matmul(concat(1, x, z), concat(0, y, w)) = ewadd(matmul(x, y), matmul(z, w))
matmulConcatMixed :: forall a. NumRule a
matmulConcatMixed _ = do
  [rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassM", "rclassK", "rclassN"]
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
  kL <- newMap "contractSI" rclassK
  kR1 <- newMap "contractSI" rclassK
  kR2 <- newMap "contractSI" rclassK
  lhs <- matmul2D xz yw [rclassK --> kL]
  xy <- matmul2D x y [rclassK --> kR1]
  zw <- matmul2D z w [rclassK --> kR2]
  rhs <- ewadd xy zw

  siRelation [kL, kR1] $ \[l, r] -> l .== r
  siRelation [kL, kR2] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR1, kR2]

  rewrite "matmul(concat(1, x, z), concat(0, y, w)) ⇒ ewadd(matmul(x, y), matmul(z, w))" lhs rhs

main :: IO ()
main = do
  -- printTitle "#################### matmulAssociativity ####################"
  -- verifyNumDSL matmulAssociativity

  -- printTitle "#################### matmulScalarLinear #####################"
  -- verifyNumDSL matmulScalarLinear

  -- printTitle "#################### matmulDistributive #####################"
  -- verifyNumDSL matmulDistributive

  -- printTitle "###################### matmulTranspose ######################"
  -- verifyNumDSL matmulTranspose

  -- printTitle "###################### matmulIdentity #######################"
  -- verifyNumDSL matmulIdentity

  -- printTitle "#################### matmulConcatRight ######################"
  -- verifyNumDSL matmulConcatRight

  printTitle "##################### matmulConcatMixed #####################"
  verifyNumDSL matmulConcatMixed
