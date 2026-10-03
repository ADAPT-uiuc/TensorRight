module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (rankPrecondition)
import qualified TensorRight.Internal.DSL.TASO as TASO

desugarEnlarge :: forall a. NumRule a
desugarEnlarge _ = do
  rclass <- newRClass "rclass"
  rankPrecondition rclass 1
  [n, c, h, w] <- newMaps ["n", "c", "h", "w"] rclass
  input <-
    newTensor
      @a
      "input"
      [ rclass --> n @@ "N",
        rclass --> c @@ "C",
        rclass --> h @@ "H",
        rclass --> w @@ "W"
      ]
  let kx = ssym "kx" :: SymInteger
      ky = ssym "ky" :: SymInteger
      hRef = ByLabel "H"
      wRef = ByLabel "W"

  hLow <- newMap "hLow" rclass
  wLow <- newMap "wLow" rclass
  lhs <- TASO.enlarge (hRef --> h) (wRef --> w) hLow wLow ky kx input

  -- These maps only define the RHS padding; TASO's domain is asserted by the
  -- backend implementation of the LHS expression.
  kH <- newConstMap "kH" ky rclass
  kW <- newConstMap "kW" kx rclass
  targetH <- combineMap "targetH" (\[original, target] -> symMax original target) [h, kH]
  targetW <- combineMap "targetW" (\[original, target] -> symMax original target) [w, kW]
  extraH <- combineMap "extraH" (\[target, original] -> target - original) [targetH, h]
  extraW <- combineMap "extraW" (\[target, original] -> target - original) [targetW, w]
  hHigh <- combineMap "hHigh" (\[extra, low] -> extra - low) [extraH, hLow]
  wHigh <- combineMap "wHigh" (\[extra, low] -> extra - low) [extraW, wLow]
  zero <- newConstMap "zero" 0 rclass

  rhs <-
    pad input (0 :: a) $
      Padding
        { low = [hRef --> hLow, wRef --> wLow],
          interior = [hRef --> zero, wRef --> zero],
          high = [hRef --> hHigh, wRef --> wHigh]
        }

  rewrite "TASO Enlarge ⇒ Pad with floor-split extra padding" lhs rhs

main :: IO ()
main = do
  putStrLn "######################## TASO enlarge ########################"
  verifyNumDSL desugarEnlarge
