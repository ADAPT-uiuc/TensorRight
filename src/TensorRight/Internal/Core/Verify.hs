{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TensorRight.Internal.Core.Verify
  ( getTensorWithValidityCondition,
    rewritingRuleAccess,
    verifyRule,
    VerifyTask (..),
    elementWiseSiRel,
  )
where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (unless, void, when)
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Foldable (traverse_)
import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T
import GHC.Generics (Generic)
import Grisette
  ( ConstantSymbolSet,
    EvalSym (evalSym),
    GrisetteSMTConfig,
    LogicalOp (symImplies, symNot, (.&&)),
    Mergeable,
    PPrint (pformat),
    SimpleMergeable,
    Solvable (con, ssym),
    SolvingFailure (Unsat),
    SymBool,
    SymEq ((.==)),
    SymInteger,
    Union,
    align,
    existsSet,
    group,
    identifier,
    nest,
    pprint,
    solve,
    vsep,
    withTimeout,
    pattern Single,
  )
import Prettyprinter.Render.Text (putDoc)
import TensorRight.Internal.Core.Axis
  ( AxisMapLike (asHashMap, fromHashMap),
    Indices,
    Sizes,
    allAxes,
    sameAxisMap,
  )
import TensorRight.Internal.Core.Tensor
  ( Tensor (BoolTensor, IntTensor, RealTensor),
    tensorAccess,
    tensorDType,
    tensorShape,
  )
import qualified TensorRight.Internal.Core.Tensor.Typed as Typed
import TensorRight.Internal.Util.Error (Error, ErrorEnv, splitWithError)
import TensorRight.Internal.Util.Pretty (printWarning)

getTensorWithValidityCondition ::
  forall a.
  (Mergeable a, Show a) =>
  String ->
  ExceptT Error Union a ->
  IO (SymBool, a)
getTensorWithValidityCondition loc a = do
  let splitted = splitWithError a
  case splitted of
    Nothing -> do
      case runExceptT a of
        Single (Left errMsg) ->
          fail $
            loc <> ": failed in all path with error message: " <> show errMsg
        _ ->
          fail $
            loc
              <> ": failed in all path, symbolic error message:\n"
              <> show (pformat (void a))
    Just (valid, Single tensor) -> return (valid, tensor)
    Just _ -> fail $ loc <> ": not merged."

data VerifyTask = VerifyTask
  { solverConfig :: GrisetteSMTConfig,
    lhsTensor :: ErrorEnv Tensor,
    rhsTensor :: ErrorEnv Tensor,
    precondition :: SymBool,
    siRelation :: SymBool,
    siRelationDiffLeft :: SymBool,
    siRelationDiffRight :: SymBool,
    siRelationNEqLeft :: SymBool,
    siRelationNEqRight :: SymBool,
    lhsSISymbols :: ConstantSymbolSet,
    rhsSISymbols :: ConstantSymbolSet,
    otherSymbols :: ConstantSymbolSet,
    dumpTensors :: [(T.Text, ErrorEnv Tensor)],
    dumpMaps :: [(T.Text, Sizes)]
  }
  deriving (Generic)

typedRewritingRuleAccess ::
  (SimpleMergeable e, SymEq e, Show e) =>
  Typed.Tensor e ->
  Typed.Tensor e ->
  Indices ->
  IO (SymBool, SymBool, SymBool)
typedRewritingRuleAccess lhsTensor rhsTensor inputIndices = do
  (lhsAccessIsValid, lhsAccessResult) <-
    getTensorWithValidityCondition "lhs-access" $
      Typed.tensorAccess lhsTensor inputIndices
  (rhsAccessIsValid, rhsAccessResult) <-
    getTensorWithValidityCondition "rhs-access" $
      Typed.tensorAccess rhsTensor inputIndices
  return
    (lhsAccessIsValid, rhsAccessIsValid, lhsAccessResult .== rhsAccessResult)

rewritingRuleAccess ::
  Tensor ->
  Tensor ->
  Indices ->
  IO (SymBool, SymBool, SymBool)
rewritingRuleAccess (RealTensor lhsTensor) (RealTensor rhsTensor) =
  typedRewritingRuleAccess lhsTensor rhsTensor
rewritingRuleAccess (IntTensor lhsTensor) (IntTensor rhsTensor) =
  typedRewritingRuleAccess lhsTensor rhsTensor
rewritingRuleAccess (BoolTensor lhsTensor) (BoolTensor rhsTensor) =
  typedRewritingRuleAccess lhsTensor rhsTensor
rewritingRuleAccess _ _ = error "Different types of tensors"

verifyRule :: VerifyTask -> IO ()
verifyRule
  ( VerifyTask
      config
      lhs
      rhs
      pre
      siRelation
      siRelationDiffLeft
      siRelationDiffRight
      siRelationNEqLeft
      siRelationNEqRight
      lhsSISymbols
      rhsSISymbols
      _otherSymbols
      dumpTensors
      dumpMaps
    ) = do
    let preCond = pre
    when (preCond == con False) $
      fail "verified (precondition is false)"

    (lhsTensorIsValid, lhsTensor) <-
      getTensorWithValidityCondition "lhs-tensor" lhs
    (rhsTensorIsValid, rhsTensor) <-
      getTensorWithValidityCondition "rhs-tensor" rhs

    when (tensorDType lhsTensor /= tensorDType rhsTensor) $
      fail "not verified (lhs and rhs have different types)"

    let inputIndices =
          fromHashMap
            $ HM.mapWithKey
              (\k _ -> ssym $ identifier $ "i[" <> T.pack (show k) <> "]")
            $ asHashMap
            $ tensorShape lhsTensor ::
            Indices
    when
      ( allAxes (tensorShape lhsTensor)
          /= allAxes (tensorShape rhsTensor)
      )
      $ fail "not verified (lhs and rhs have different dimensions)"

    let shapeEqualCond =
          sameAxisMap
            (tensorShape lhsTensor)
            (tensorShape rhsTensor)

    (lhsAccessIsValid, rhsAccessIsValid, rewriteEquivalent) <-
      rewritingRuleAccess lhsTensor rhsTensor inputIndices

    wpCheckSol1 <-
      solve
        config
        ( symNot preCond
            .&& lhsTensorIsValid
            .&& rhsTensorIsValid
            .&& lhsAccessIsValid
            .&& rhsAccessIsValid
            .&& shapeEqualCond
            .&& rewriteEquivalent
        )
    case wpCheckSol1 of
      Left Unsat -> putStrLn "  Pre-condition is weakest."
      Left err -> fail $ "  Solver failed with error: " <> show err
      Right _ -> putStrLn "  Pre-condition is stronger than needed."

    wpCheckSol2 <-
      solve
        config
        ( preCond
            .&& lhsTensorIsValid
            .&& rhsTensorIsValid
            .&& lhsAccessIsValid
            .&& rhsAccessIsValid
            .&& shapeEqualCond
            .&& rewriteEquivalent
        )
    case wpCheckSol2 of
      Left Unsat -> putStrLn "  Pre-condition rules out all valid inputs (Or the rule is symbolically invalid)."
      Left err -> fail $ "  Solver failed with error: " <> show err
      Right _ -> putStrLn "  Pre-condition allows at least one valid input, on which LHS=RHS."

    let dump model = do
          putDoc $ "  Input indices: " <> pformat (evalSym True model inputIndices) <> "\n"
          putDoc $ "  Lhs access: " <> pformat (evalSym True model $ tensorAccess lhsTensor inputIndices) <> "\n"
          putDoc $ "  Rhs access: " <> pformat (evalSym True model $ tensorAccess rhsTensor inputIndices) <> "\n"
          putDoc $ "  Lhs shape: " <> pformat (evalSym True model $ tensorShape lhsTensor) <> "\n"
          putDoc $ "  Rhs shape: " <> pformat (evalSym True model $ tensorShape rhsTensor) <> "\n"
          putStrLn $
            "  Conditions (lhsAccessIsValid): "
              <> show (evalSym True model lhsAccessIsValid)
          putStrLn $
            "  Conditions (rhsAccessIsValid): "
              <> show (evalSym True model rhsAccessIsValid)
          putStrLn $
            "  Conditions (lhsTensorIsValid): "
              <> show (evalSym True model lhsTensorIsValid)
          putStrLn $
            "  Conditions (rhsTensorIsValid): "
              <> show (evalSym True model rhsTensorIsValid)
          putStrLn $
            "  Conditions (shapeEqualCond): "
              <> show (evalSym True model shapeEqualCond)
          putStrLn $
            "  Conditions (rewriteEquivalent): "
              <> show (evalSym True model rewriteEquivalent)
          putStrLn (replicate 80 '-')
          traverse_
            ( \(name, tensor) -> do
                (valid, t) <-
                  getTensorWithValidityCondition (T.unpack name) tensor
                putDoc $
                  "  "
                    <> pformat name
                    <> "(validate): "
                    <> pformat (evalSym True model valid)
                    <> "\n"
                putDoc $
                  "  "
                    <> align
                      ( nest 2 $
                          group $
                            vsep
                              [ pformat name
                                  <> "(shape):",
                                pformat (evalSym True model $ tensorShape t)
                              ]
                      )
                    <> "\n"
            )
            dumpTensors
          traverse_
            ( \(name, map) -> do
                putDoc $
                  "  "
                    <> align
                      ( nest 2 $
                          group $
                            vsep
                              [ pformat name <> "(map):",
                                pformat (evalSym True model map)
                              ]
                      )
                    <> "\n"
            )
            dumpMaps
          putStrLn (replicate 80 '-')
          pprint model
    -- putDoc $ "Raw model: " <> pformat model <> "\n"

    -- Check if the si-relation is bijective
    when (lhsSISymbols /= mempty && rhsSISymbols /= mempty) $ do
      condl2r <-
        evaluate $
          force $
            preCond
              .&& siRelation
              .&& lhsTensorIsValid
              .&& lhsAccessIsValid
              .&& rhsTensorIsValid
              .&& rhsAccessIsValid
              .&& siRelationDiffLeft
              .&& siRelationNEqLeft
      soll2r <- solve config condl2r
      bil2r <- case soll2r of
        Left Unsat -> return True
        Left err -> do
          printWarning $ "Verification for forall right si there do not exist multiple left si fails due to unexpected solver failure" <> show err
          return False
        Right m -> do
          pprint m
          printWarning $ "SI-relation is not bijective. (There exist multiple left SI for a right SI.)"
          return False

      condr2l <-
        evaluate $
          force $
            preCond
              .&& siRelation
              .&& lhsTensorIsValid
              .&& lhsAccessIsValid
              .&& rhsTensorIsValid
              .&& rhsAccessIsValid
              .&& siRelationDiffRight
              .&& siRelationNEqRight
      solr2l <- solve config condr2l
      bir2l <- case solr2l of
        Left Unsat -> return True
        Left err -> do
          printWarning $ "Verification for forall left si there do not exist multiple right si fails due to unexpected solver failure" <> show err
          return False
        Right m -> do
          pprint m
          printWarning $ "SI-relation is not bijective. (There exist multiple right SI for a left SI.)"
          return False

      if bil2r && bir2l
        then do
          condl <-
            evaluate $
              force $
                preCond
                  .&& lhsTensorIsValid
                  .&& lhsAccessIsValid
                  .&& symNot
                    ( existsSet rhsSISymbols $
                        siRelation
                          .&& rhsAccessIsValid
                          .&& rhsTensorIsValid
                    )
          r <- solve (withTimeout 5000000 config) condl
          allokl <- case r of
            Left Unsat -> return True
            Left err -> do
              printWarning $ "Verification that all left si can be accessed fails due to unexpected solver failure" <> show err
              return False
            Right m -> do
              pprint m
              printWarning $ "Some left si cannot be accessed."
              return False
          condr <-
            evaluate $
              force $
                preCond
                  .&& rhsTensorIsValid
                  .&& rhsAccessIsValid
                  .&& symNot
                    ( existsSet lhsSISymbols $
                        siRelation
                          .&& lhsAccessIsValid
                          .&& lhsTensorIsValid
                    )
          r <- solve (withTimeout 5000000 config) condr
          allokr <- case r of
            Left Unsat -> return True
            Left err -> do
              printWarning $ "Verification that all right si can be accessed fails due to unexpected solver failure" <> show err
              return False
            Right m -> do
              pprint m
              printWarning $ "Some right si cannot be accessed."
              return False
          unless (allokl && allokr) $
            printWarning $ "Some SI cannot be accessed."
        else printWarning $ "SI-relation is not bijective."

    cond1 <-
      evaluate $
        force $
          symNot $
            symImplies
              (preCond .&& siRelation .&& lhsTensorIsValid)
              ( symImplies
                  lhsAccessIsValid
                  ( rhsTensorIsValid
                      .&& rhsAccessIsValid
                      .&& shapeEqualCond
                      .&& rewriteEquivalent
                  )
              )
    sol1 <- solve config cond1
    case sol1 of
      Left Unsat -> putStrLn "  Verified forall left si exists right si."
      Left err -> fail $ "  Verification for forall left si exists right si fails due to unexpected solver failure" <> show err
      Right model -> do
        dump model
        fail "  Not verified forall left si exists right si."

    when (lhsSISymbols /= mempty || rhsSISymbols /= mempty) $ do
      cond2 <-
        evaluate $
          force $
            symNot $
              symImplies
                (preCond .&& siRelation .&& rhsTensorIsValid)
                ( symImplies
                    rhsAccessIsValid
                    ( lhsTensorIsValid
                        .&& lhsAccessIsValid
                        .&& shapeEqualCond
                        .&& rewriteEquivalent
                    )
                )

      sol2 <- solve config cond2
      case sol2 of
        Left Unsat -> putStrLn "  Verified forall right si exists left si."
        Left err -> fail $ "  Verification for forall right si exists left si fails due to unexpected solver failure" <> show err
        Right model -> do
          dump model
          fail "  Not verified forall right si exists left si."

elementWiseSiRel ::
  (SymInteger -> SymInteger -> SymBool) ->
  Indices ->
  Indices ->
  SymBool
elementWiseSiRel f m1 m2 =
  con (allAxes m1 == allAxes m2)
    .&& foldr
      (.&&)
      (con True)
      (HM.intersectionWith f (asHashMap m1) (asHashMap m2))
