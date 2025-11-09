{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module TensorRight.Internal.DSL.BoundInference (inferBound) where

import Control.Monad (when)
import Control.Monad.State (State, execState, modify)
import Data.Function (on)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List (groupBy, sortOn)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.String (IsString (fromString))
import qualified Data.Text as T
import Data.Typeable (cast)
import GHC.Generics (Generic)
import Grisette
  ( Default (Default),
    GrisetteSMTConfig,
    Identifier (Identifier),
    LinkedRep (underlyingTerm),
    LogicalOp ((.&&)),
    PPrint,
    SExpr (List),
    Solvable (con, ssym),
    SolvingFailure (Unsat),
    SomeTerm (SomeTerm),
    SymBool (SymBool),
    SymEq ((./=)),
    Symbol (SimpleSymbol),
    Term,
    TypedSymbol (TypedSymbol, unTypedSymbol),
    solve,
    someTermSize,
    withMetadata,
    pattern ApplyTerm,
    pattern ConTerm,
    pattern DistinctTerm,
    pattern Metadata,
    pattern SubTerms,
    pattern SymTerm,
  )
import TensorRight.Internal.Core.Axis
  ( Axis (Axis, LabelledAxis),
    AxisMapLike (fromHashMap),
    Indices,
  )
import TensorRight.Internal.Core.Tensor (tensorDType)
import TensorRight.Internal.Core.Verify
  ( VerifyTask (VerifyTask),
    getTensorWithValidityCondition,
    rewritingRuleAccess,
  )
import TensorRight.Internal.DSL.Eval
  ( SymIdentInfo (SymMap, SymTensor),
    getAxisName,
  )
import TensorRight.Internal.DSL.Identifier (RClassIdentifier, TensorIdentifier)
import TensorRight.Internal.DSL.Shape
  ( AbstractShape
      ( AbstractShape,
        labelled,
        unlabelled
      ),
  )

newtype AnalysisState = AnalysisState
  { termRClassTensors ::
      HM.HashMap
        SomeTerm
        (HS.HashSet RClassIdentifier, HS.HashSet TensorIdentifier)
  }
  deriving (Show, Generic)
  deriving (PPrint) via (Default AnalysisState)

hasRClass :: AnalysisState -> RClassIdentifier -> SomeTerm -> Bool
hasRClass AnalysisState {..} rclass st =
  case HM.lookup st termRClassTensors of
    Just (rclasses, _) -> HS.member rclass rclasses
    Nothing -> error "Term not found"

analysisTerm :: SomeTerm -> AnalysisState
analysisTerm someTerm =
  execState (analysisTermState someTerm) (AnalysisState HM.empty)

analysisTermState ::
  SomeTerm ->
  State AnalysisState (HS.HashSet RClassIdentifier, HS.HashSet TensorIdentifier)
analysisTermState someTerm = do
  (rclasses, tensors) <- analysisTermState' someTerm
  modify
    ( \s ->
        s
          { termRClassTensors =
              HM.insert someTerm (rclasses, tensors) (termRClassTensors s)
          }
    )
  return (rclasses, tensors)

analysisTermState' ::
  SomeTerm ->
  State AnalysisState (HS.HashSet RClassIdentifier, HS.HashSet TensorIdentifier)
analysisTermState' (SomeTerm t) = do
  case t of
    ConTerm {} -> return (HS.empty, HS.empty)
    SymTerm symb -> case unTypedSymbol symb of
      SimpleSymbol (Identifier _ (List [])) ->
        return (HS.empty, HS.empty)
      SimpleSymbol (Identifier _ meta) ->
        case meta of
          Metadata (SymMap rclass _ _) -> do
            return (HS.singleton rclass, HS.empty)
          Metadata (SymTensor t) -> do
            return (HS.empty, HS.singleton t)
          _ -> error $ "Unexpected metadata: " <> show meta
      _ -> return (HS.empty, HS.empty)
    SubTerms ts -> do
      r <- traverse analysisTermState ts
      return $ mconcat r

getAllConditions :: AnalysisState -> SomeTerm -> HS.HashSet SomeTerm
getAllConditions state@AnalysisState {..} st@(SomeTerm t) =
  case HM.lookup st termRClassTensors of
    Just (rclasses, _) | HS.null rclasses -> HS.empty
    Just (_, tensors) | HS.null tensors ->
      case cast t of
        Just (_ :: Term Bool) -> HS.singleton st
        Nothing -> goBody t
    Just _ -> goBody t
    Nothing -> error "Term not found"
  where
    goSome :: SomeTerm -> HS.HashSet SomeTerm
    goSome = getAllConditions state
    goBody :: forall a. Term a -> HS.HashSet SomeTerm
    goBody (ConTerm _) = error "Should not happen"
    goBody (SymTerm _) = error "Should not happen"
    goBody ApplyTerm {} = HS.empty
    goBody (SubTerms ts) = mconcat $ goSome <$> ts

getAllAccesses :: AnalysisState -> SomeTerm -> HS.HashSet SomeTerm
getAllAccesses state@AnalysisState {..} st@(SomeTerm t) =
  case t of
    ConTerm _ -> HS.empty
    SymTerm _ -> HS.empty
    ApplyTerm {} -> HS.singleton st
    SubTerms ts -> mconcat $ go <$> ts
  where
    go :: SomeTerm -> HS.HashSet SomeTerm
    go = getAllAccesses state

conditionEquivalent ::
  GrisetteSMTConfig -> SymBool -> SomeTerm -> SomeTerm -> IO Bool
conditionEquivalent solverConfig allPreCond (SomeTerm l) (SomeTerm r) =
  case (cast l, cast r) of
    (Just (a11 :: Term Bool), Just (a12 :: Term Bool)) -> do
      r <-
        solve solverConfig (allPreCond .&& SymBool a11 ./= SymBool a12)
      case r of
        Left Unsat -> return True
        Left err -> fail $ "Unexpected solver failure: " <> show err
        Right _ -> return False
    _ -> error "Not conditions"

accessEquivalent ::
  GrisetteSMTConfig -> SymBool -> SomeTerm -> SomeTerm -> IO Bool
accessEquivalent solverConfig allPreCond (SomeTerm l) (SomeTerm r) =
  case (l, r) of
    (ApplyTerm (f1 :: Term f1) (args1 :: Term args1), ApplyTerm f2 args2) ->
      case (cast f2, cast args2) of
        (Just (f2' :: Term f1), _) | f1 /= f2' -> return False
        (Just (_ :: Term f1), Just (args2' :: Term args1)) -> do
          r <-
            solve
              solverConfig
              (allPreCond .&& SymBool (DistinctTerm (args1 :| [args2'])))
          case r of
            Left Unsat -> return True
            Left err -> fail $ "Unexpected solver failure: " <> show err
            Right _ -> return False
        _ -> return False
    _ -> error "Not accesses"

filterPairs ::
  (SomeTerm -> SomeTerm -> IO Bool) ->
  HS.HashSet SomeTerm ->
  IO (HS.HashSet SomeTerm)
filterPairs eqv conditions = do
  HS.fromList <$> go (sortOn (\x -> -someTermSize x) $ HS.toList conditions)
  where
    go [] = return []
    go (x : xs) = do
      r <- go1 x xs
      t <- go xs
      if r
        then return t
        else return (x : t)
    go1 _ [] = return False
    go1 x (y : ys) = do
      r <- eqv x y
      rs <- go1 x ys
      return $ r || rs

groupAccessByTensors :: [SomeTerm] -> [[SomeTerm]]
groupAccessByTensors = groupBy (on (==) termTensor) . sortOn termTensor
  where
    termTensor :: SomeTerm -> TensorIdentifier
    termTensor
      ( SomeTerm
          ( ApplyTerm
              ( SymTerm
                  ( TypedSymbol
                      (SimpleSymbol (Identifier _ (Metadata (SymTensor t))))
                    )
                )
              _
            )
        ) = t
    termTensor _ = error "Should not happen"

inferBound ::
  GrisetteSMTConfig ->
  VerifyTask ->
  HS.HashSet RClassIdentifier ->
  HM.HashMap RClassIdentifier Int ->
  AbstractShape ->
  IO (HM.HashMap RClassIdentifier (Int, Int))
inferBound
  solverConfig
  (VerifyTask _ lhs rhs pre siRelation _ _ _ _ _ _ _ _ _)
  nonFixedRClasses
  rankConditions
  sp = do
    let preCond = pre
    when (preCond == con False) $
      fail "verified (precondition is false)"

    (lhsTensorIsValid, lhsTensor) <-
      getTensorWithValidityCondition "lhs-tensor" lhs
    (rhsTensorIsValid, rhsTensor) <-
      getTensorWithValidityCondition "rhs-tensor" rhs

    when (tensorDType lhsTensor /= tensorDType rhsTensor) $
      fail "not verified (lhs and rhs have different types)"
    let access = abstractShapeAccess sp

    (lhsAccessIsValid, rhsAccessIsValid, equivalent) <-
      rewritingRuleAccess lhsTensor rhsTensor access
    let st = analysisTerm $ SomeTerm $ underlyingTerm equivalent
    let allPreCond =
          preCond
            .&& siRelation
            .&& lhsTensorIsValid
            .&& rhsTensorIsValid
            .&& lhsAccessIsValid
            .&& rhsAccessIsValid
    let allConditions =
          getAllConditions st $
            SomeTerm $
              underlyingTerm equivalent
    filteredConditions <-
      filterPairs (conditionEquivalent solverConfig allPreCond) allConditions
    let allAccesses = getAllAccesses st $ SomeTerm $ underlyingTerm equivalent
    filteredAccesses <- filterPairs (accessEquivalent solverConfig allPreCond) allAccesses
    putStrLn $ "# all conditions: " <> show (HS.size allConditions)
    putStrLn $ "# all accesses: " <> show (HS.size allAccesses)
    putStrLn $ "# filtered conditions: " <> show (HS.size filteredConditions)
    putStrLn $ "# filtered accesses: " <> show (HS.size filteredAccesses)
    let groupedAccesses = groupAccessByTensors $ HS.toList filteredAccesses

    let numHasRClassInGroup :: RClassIdentifier -> [SomeTerm] -> Int
        numHasRClassInGroup rclass = length . filter (hasRClass st rclass)
        factorial :: Int -> Int
        factorial 0 = 1
        factorial n = n * factorial (n - 1)
        kFromAccess :: RClassIdentifier -> [SomeTerm] -> Int
        kFromAccess rclass group = case numHasRClassInGroup rclass group of
          v | v < 2 -> 0
          v -> factorial v `div` 2 `div` factorial (v - 2)

    let kFromAllAccesses rclass = sum $ kFromAccess rclass <$> groupedAccesses
    let kForRClass rclass =
          max 1 $
            kFromAllAccesses rclass
              + numHasRClassInGroup rclass (HS.toList filteredConditions)

    let fixedRClasses = HM.keysSet rankConditions
    let inferredBounds =
          HM.fromList $
            (\rclass -> (rclass, (1, kForRClass rclass)))
              <$> HS.toList (nonFixedRClasses `HS.difference` fixedRClasses)
    return $ HM.union inferredBounds (HM.map (\k -> (k, k)) rankConditions)

abstractShapeAccess :: AbstractShape -> Indices
abstractShapeAccess AbstractShape {..} = do
  fromHashMap $ unlabelledRClassAccesses <> labelledRClassAccess
  where
    unlabelledRClassAccesses =
      HM.fromList $
        ( \rclass ->
            ( Axis $ getAxisName rclass 0,
              ssym $
                withMetadata "access" $
                  SymMap rclass 0 "#accnolabel"
            )
        )
          <$> HS.toList unlabelled
    labelledRClassAccess =
      HM.fromList $
        ( \(label, rclass) ->
            ( LabelledAxis label $ getAxisName rclass 0,
              ssym $
                withMetadata "access" $
                  SymMap rclass 0 $
                    fromString $
                      T.unpack label
            )
        )
          <$> HM.toList labelled
