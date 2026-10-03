module Main (main) where

import Data.Foldable (traverse_)
import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (rankPrecondition)
import qualified TensorRight.Internal.DSL.TASO as TASO

desugarEnlarge :: forall a. NumRule a
desugarEnlarge _ = do
  [batch, channel, height, width] <- newRClasses ["batch", "channel", "height", "width"]
  traverse_ (`rankPrecondition` 1) [batch, channel, height, width]
  n <- newMap "n" batch
  c <- newMap "c" channel
  sourceH <- newMap "sourceH" height
  sourceW <- newMap "sourceW" width
  referenceH <- newMap "referenceH" height
  referenceW <- newMap "referenceW" width
  source <-
    newTensor
      @a
      "source"
      [ batch --> n,
        channel --> c,
        height --> sourceH,
        width --> sourceW
      ]
  reference <-
    newTensor
      @a
      "reference"
      [ batch --> n,
        channel --> c,
        height --> referenceH,
        width --> referenceW
      ]
  let hRef = ByRClass height
      wRef = ByRClass width

  lhs <- TASO.enlarge hRef wRef source reference

  -- These maps define the Pad configuration. They do not define TASO
  -- enlarge's validity domain: Core asserts that reference dimensions do not
  -- shrink the source.
  hLow <- newMap "hLow" height
  wLow <- newMap "wLow" width
  precondition [hLow, referenceH, sourceH] $ \[low, target, original] ->
    2 * low .<= target - original .&& target - original .<= 2 * low + 1
  precondition [wLow, referenceW, sourceW] $ \[low, target, original] ->
    2 * low .<= target - original .&& target - original .<= 2 * low + 1
  extraH <- combineMap "extraH" (\[target, original] -> target - original) [referenceH, sourceH]
  extraW <- combineMap "extraW" (\[target, original] -> target - original) [referenceW, sourceW]
  hHigh <- combineMap "hHigh" (\[extra, low] -> extra - low) [extraH, hLow]
  wHigh <- combineMap "wHigh" (\[extra, low] -> extra - low) [extraW, wLow]
  zeroH <- newConstMap "zeroH" 0 height
  zeroW <- newConstMap "zeroW" 0 width

  rhs <-
    pad source (0 :: a) $
      Padding
        { low = [hRef --> hLow, wRef --> wLow],
          interior = [hRef --> zeroH, wRef --> zeroW],
          high = [hRef --> hHigh, wRef --> wHigh]
        }

  rewrite "TASO Enlarge ⇒ Pad with floor-split extra padding" lhs rhs

main :: IO ()
main = do
  putStrLn "######################## TASO enlarge ########################"
  verifyNumDSLWith (withTimeout 5000000 z3) desugarEnlarge
