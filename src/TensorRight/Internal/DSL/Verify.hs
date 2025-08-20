{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module TensorRight.Internal.DSL.Verify
  ( verifyDSL,
    verifyDSLWith,
    verifyAnyDTypeDSL,
    verifyAnyDTypeDSLWith,
    verifyNumDSL,
    verifyNumDSLWith,
  )
where

import Control.Exception (SomeException, handle)
import Control.Monad (when, (>=>))
import Control.Monad.Except (runExceptT)
import Control.Monad.State (evalState)
import Data.Data (Proxy (Proxy))
import Data.Either (isRight)
import Data.Foldable (Foldable (toList), traverse_)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe (fromJust)
import qualified Data.Set.Ordered as OS
import qualified Data.Text as T
import GHC.Clock (getMonotonicTime)
import Grisette
  ( ExtractSym (extractSymMaybe),
    GrisetteSMTConfig,
    LogicalOp ((.&&)),
    Solvable (con, ssym),
    SymBool,
    simpleMerge,
    symAnd,
    withMetadata,
    z3,
  )
import TensorRight.Internal.Core.Axis (Axis (Axis), AxisMapLike (fromHashMap))
import TensorRight.Internal.Core.Tensor (numTensorAssumption)
import TensorRight.Internal.Core.Tensor.TensorInt (TensorInt, TensorReal)
import TensorRight.Internal.Core.Verify (VerifyTask (VerifyTask), verifyRule)
import TensorRight.Internal.DSL.BoundInference (inferBound)
import TensorRight.Internal.DSL.Condition (Condition (Condition))
import TensorRight.Internal.DSL.DSL
  ( DSLContext,
    Env
      ( Env,
        declaredRClasses,
        exprAbstractShapes,
        lhsSIMaps,
        numTensorAssumptions,
        preConditions,
        rhsSIMaps,
        singletonRClasses,
        tensorShapes
      ),
    ValidElem,
    ValidNum,
    mapRClasses,
    runDSLContext,
    siRelations,
    tensorDTypes,
  )
import TensorRight.Internal.DSL.Eval
  ( EvalState
      ( EvalState,
        allTensorDTypes,
        allTensorShapes,
        evaluated,
        exprShapes,
        maps,
        rclasses
      ),
    SymIdentInfo (SymMap),
    eval,
    evalRewrite,
    getAxisMapLike,
    getAxisName,
    modifyMaps,
  )
import TensorRight.Internal.DSL.Expr
  ( Env (monitoringExprs, monitoringMaps),
    NumTensorAssumption (NumTensorAssumption),
    Rewrite,
    exprId,
    lhs,
    name,
  )
import TensorRight.Internal.DSL.Identifier (RClassIdentifier)
import TensorRight.Internal.DSL.Shape
  ( AbstractShape,
  )

verifyDSLWithNDim ::
  GrisetteSMTConfig ->
  Rewrite ->
  Env ->
  HM.HashMap RClassIdentifier Int ->
  IO (VerifyTask, HS.HashSet RClassIdentifier, HS.HashSet RClassIdentifier, AbstractShape)
verifyDSLWithNDim solverConfig rewrite Env {..} ndim = do
  putStrLn $ "Verifying with ndim: " <> show ndim
  let rclasses =
        HM.fromList $
          ( \rclassIdent ->
              ( rclassIdent,
                OS.fromList
                  [0 .. ndim HM.! rclassIdent - 1]
              )
          )
            <$> HS.toList declaredRClasses
  let maps =
        HM.fromList $
          ( \(mapIdent, rclassIdent) ->
              let rclassAxes = rclasses HM.! rclassIdent
                  identForAxis i = withMetadata "map" $ SymMap rclassIdent i mapIdent
               in ( mapIdent,
                    HM.fromList
                      [ ( getAxisName rclassIdent axis,
                          ssym $ identForAxis axis
                        )
                      | axis <- toList rclassAxes
                      ]
                  )
          )
            <$> HM.toList mapRClasses
  let evalInitialState =
        EvalState
          { allTensorShapes = tensorShapes,
            allTensorDTypes = tensorDTypes,
            evaluated = HM.empty,
            exprShapes = exprAbstractShapes,
            ..
          }
  let ((lhsTensor, rhsTensor), monitoringTensors, monitoringSizes, assumptions) =
        evalState
          ( do
              r <- evalRewrite rewrite
              monitoringTensors <-
                traverse
                  (\(name, expr) -> (name,) <$> eval expr)
                  (reverse monitoringExprs)
              monitoringSizes <-
                traverse
                  (\(name, rclassref, map) -> (name,) <$> getAxisMapLike rclassref map)
                  (reverse monitoringMaps)
              assumptions <-
                traverse
                  ( \(NumTensorAssumption exprs map f) -> do
                      evaledExprs <- traverse eval exprs
                      return $
                        numTensorAssumption
                          evaledExprs
                          (fromHashMap $ HM.mapKeys Axis $ maps HM.! map)
                          f
                  )
                  numTensorAssumptions
              let allAssumptions =
                    simpleMerge $ do
                      v <- runExceptT $ symAnd <$> sequence assumptions
                      case v of
                        Left _ -> con True
                        Right a -> return a

              return (r, monitoringTensors, monitoringSizes, allAssumptions)
          )
          evalInitialState

  let instantiateCondition maps (Condition conditionInputs condition) =
        condition $ fmap (maps HM.!) conditionInputs
  let instantiatedPreconditions =
        symAnd $ fmap (instantiateCondition maps) preConditions
  let instantiatedSIRelations =
        symAnd $ fmap (instantiateCondition maps) siRelations
  when (not (null siRelations) && null lhsSIMaps && null rhsSIMaps) $
    fail "[FAIL] No maps provided for SI relations. Use checkSIMap."
  let (lhsNeq, modifiedlhsMap) = modifyMaps "lhs" lhsSIMaps maps
  let siDiffLeft =
        symAnd $ fmap (instantiateCondition modifiedlhsMap) siRelations
  let (rhsNeq, modifiedrhsMap) = modifyMaps "rhs" rhsSIMaps maps
  let siDiffRight =
        symAnd $ fmap (instantiateCondition modifiedrhsMap) siRelations
  let lhsSISymbols =
        HM.foldMapWithKey
          ( \k m ->
              if k `HS.member` lhsSIMaps
                then fromJust $ extractSymMaybe $ HM.toList m
                else mempty
          )
          maps
  let rhsSISymbols =
        HM.foldMapWithKey
          ( \k m ->
              if k `HS.member` rhsSIMaps
                then fromJust $ extractSymMaybe $ HM.toList m
                else mempty
          )
          maps
  let otherSISymbols =
        HM.foldMapWithKey
          ( \k m ->
              if not (k `HS.member` lhsSIMaps || k `HS.member` rhsSIMaps)
                then fromJust $ extractSymMaybe $ HM.toList m
                else mempty
          )
          maps
  return
    ( VerifyTask
        solverConfig
        lhsTensor
        rhsTensor
        (instantiatedPreconditions .&& assumptions)
        instantiatedSIRelations
        siDiffLeft
        siDiffRight
        lhsNeq
        rhsNeq
        lhsSISymbols
        rhsSISymbols
        otherSISymbols
        monitoringTensors
        monitoringSizes,
      declaredRClasses `HS.difference` singletonRClasses,
      singletonRClasses,
      exprAbstractShapes HM.! exprId (lhs rewrite)
    )

baseRClassBound0 :: Rewrite -> Env -> HM.HashMap RClassIdentifier Int
baseRClassBound0 _ Env {..} =
  HM.fromList ((,1) <$> HS.toList declaredRClasses)

getRewriteName :: DSLContext Rewrite -> Either T.Text T.Text
getRewriteName rewrite = case runDSLContext rewrite of
  Left err -> Left err
  Right (rewrite, _) -> Right $ name rewrite

printRewriteNameLine :: DSLContext Rewrite -> IO ()
printRewriteNameLine rewrite = do
  case getRewriteName rewrite of
    Left err -> fail $ T.unpack err
    Right name -> putStrLn $ "====> " <> T.unpack name

data Result = Result
  { elapsedTime :: Double,
    result :: Either SomeException ()
  }

instance Semigroup Result where
  Result t1 r1 <> Result t2 r2 =
    Result (t1 + t2) (r1 >> r2)

printResult :: Maybe String -> Result -> IO ()
printResult subTheory Result {..} =
  putStrLn $
    ( if isRight result
        then "\ESC[32m" <> "[" <> "SUCCESS"
        else "\ESC[31m" <> "[" <> "FAIL"
    )
      <> maybe "" ("-" <>) subTheory
      <> "]: ["
      <> show elapsedTime
      <> "s] Verification "
      <> (if isRight result then "succeeded" <> "\ESC[0m" else "failed" <> "\ESC[0m")
      <> ( case result of
             Right () -> "."
             Left e -> " with error: " <> show e
         )

bracketFailure ::
  DSLContext Rewrite -> IO () -> IO Result
bracketFailure rewrite action = do
  case getRewriteName rewrite of
    Left err -> do
      putStrLn "The rule isn't valid (does not type check)"
      fail $ T.unpack err
    Right name -> do
      putStrLn $ "Verifying rule " <> T.unpack name
      startTime <- getMonotonicTime
      handle
        ( \(e :: SomeException) -> do
            endTime <- getMonotonicTime
            let elapsedTime = endTime - startTime
            return $ Result elapsedTime $ Left e
        )
        $ do
          action
          endTime <- getMonotonicTime
          let elapsedTime = endTime - startTime
          return $ Result elapsedTime $ Right ()

verifyDSLWithImpl :: GrisetteSMTConfig -> Maybe String -> DSLContext Rewrite -> IO ()
verifyDSLWithImpl solverConfig theoryInfo rewrite = do
  case runDSLContext rewrite of
    Left err -> fail $ T.unpack err
    Right (rewrite, env) -> do
      putStrLn $ "Verifying rule " <> T.unpack (name rewrite)
      let bound0 = baseRClassBound0 rewrite env
      (task, nonSingletonRClasses, singletonRClasses, shape) <-
        verifyDSLWithNDim solverConfig rewrite env bound0
      inferredBound <-
        inferBound
          solverConfig
          task
          nonSingletonRClasses
          singletonRClasses
          shape
      putStrLn $ "Inferred bounds: " <> show inferredBound
      putStrLn $
        "[INFO"
          <> maybe "" ("-" <>) theoryInfo
          <> "]: Inferred bounds: "
          <> show inferredBound
      putStrLn $
        "[INFO"
          <> maybe "" ("-" <>) theoryInfo
          <> "]: Number of bounded verification tasks: "
          <> show (product inferredBound)
      let ndims = allNdims $ HM.toList inferredBound
      let fst4 (a, _, _, _) = a
      traverse_
        (verifyDSLWithNDim solverConfig rewrite env >=> verifyRule . fst4)
        ndims
  where
    allNdims :: [(RClassIdentifier, Int)] -> [HM.HashMap RClassIdentifier Int]
    allNdims inferredBoundList =
      HM.fromList
        <$> traverse
          ( \(rclassIdent, bound) ->
              [(rclassIdent, i) | i <- [1 .. bound]]
          )
          inferredBoundList

-- | Verify a DSL rule with inferred bounds.
verifyDSL :: DSLContext Rewrite -> IO ()
verifyDSL = verifyDSLWith z3

-- | Verify a DSL rule with a given solver configuration.
verifyDSLWith :: GrisetteSMTConfig -> DSLContext Rewrite -> IO ()
verifyDSLWith config rewrite = do
  printRewriteNameLine rewrite
  bracketFailure rewrite (verifyDSLWithImpl config Nothing rewrite)
    >>= printResult Nothing

verifyAnyDTypeDSLWith ::
  GrisetteSMTConfig -> (forall a p. (ValidElem a) => p a -> DSLContext Rewrite) -> IO ()
verifyAnyDTypeDSLWith solverConfig rewrite = do
  printRewriteNameLine (rewrite (Proxy @TensorInt))
  putStrLn ">>> Bool"
  br <-
    bracketFailure (rewrite (Proxy @SymBool)) $
      verifyDSLWithImpl solverConfig (Just "Bool") (rewrite (Proxy @SymBool))
  printResult (Just "Bool") br
  putStrLn ">>> Int"
  ir <-
    bracketFailure (rewrite (Proxy @TensorInt)) $
      verifyDSLWithImpl solverConfig (Just "Int") (rewrite (Proxy @TensorInt))
  printResult (Just "Int") ir
  putStrLn ">>> Real"
  rr <-
    bracketFailure (rewrite (Proxy @TensorReal)) $
      verifyDSLWithImpl solverConfig (Just "Real") (rewrite (Proxy @TensorReal))
  printResult (Just "Real") rr
  putStrLn ">>> Overall"
  printResult (Just "Overall") $ br <> ir <> rr

verifyAnyDTypeDSL :: (forall a p. (ValidElem a) => p a -> DSLContext Rewrite) -> IO ()
verifyAnyDTypeDSL = verifyAnyDTypeDSLWith z3

verifyNumDSLWith ::
  GrisetteSMTConfig -> (forall a p. (ValidNum a) => p a -> DSLContext Rewrite) -> IO ()
verifyNumDSLWith solverConfig rewrite = do
  printRewriteNameLine (rewrite (Proxy @TensorInt))
  putStrLn ">>> Int"
  ir <-
    bracketFailure (rewrite (Proxy @TensorInt)) $
      verifyDSLWithImpl solverConfig (Just "Int") (rewrite (Proxy @TensorInt))
  printResult (Just "Int") ir
  putStrLn ">>> Real"
  rr <-
    bracketFailure (rewrite (Proxy @TensorReal)) $
      verifyDSLWithImpl solverConfig (Just "Real") (rewrite (Proxy @TensorReal))
  printResult (Just "Real") rr
  putStrLn ">>> Overall"
  printResult (Just "Overall") $ ir <> rr

verifyNumDSL :: (forall a p. (ValidNum a) => p a -> DSLContext Rewrite) -> IO ()
verifyNumDSL = verifyNumDSLWith z3
