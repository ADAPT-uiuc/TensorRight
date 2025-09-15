{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module TensorRight.Internal.DSL.Shape
  ( TensorShape (..),
    RClassRef (..),
    RClassRefSet,
    AbstractShape (..),
    toAbstractShape,
    TensorShapeLike (toTensorShape),
    TensorShapeDesc (..),
    abstractShapeAllRefs,
    removeRClass,
    getRClassByRClassRef,
    addRClassByRClassRef,
    concatAbstractShape,
    restrictAbstractShape,
  )
where

import Control.Monad (when)
import Control.Monad.Error.Class (MonadError (throwError))
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Hashable (Hashable (hashWithSalt))
import Data.List (sortBy)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Grisette (Default (Default), PPrint (pformat, pformatPrec), TryMerge)
import TensorRight.Internal.DSL.Identifier (Label, MapIdentifier, RClassIdentifier)
import TensorRight.Internal.DSL.Syntax (ArrowSyntax ((-->)), AtSyntax ((@@)))
import TensorRight.Internal.Util.Error (Error, assert)
import TensorRight.Internal.Util.Pretty (encloseList, prettyWithConstructor)

-- | Reference to an RClass, also referred to as an aggregated-axis in our DSL.
-- An RClass may be labelled or unlabelled.
-- If an RClass is unlabelled, then it means that the RClass has exactly
-- one-aggregated-axis, and the RClass itself acts as a reference to the
-- said aggregated-axis.
-- If the RClass is labelled, then the label acts as a reference to the
-- aggregated-axis. In this case, the RClass can have multiple labels,
-- each referring to a different aggregated-axis on that RClass.
data RClassRef
  = ByRClass RClassIdentifier
  | ByLabel Label
  deriving (Generic, Eq, Ord, Show)
  deriving (Hashable)
  deriving (PPrint) via (Default RClassRef)

type RClassRefSet = HS.HashSet RClassRef

-- | A Tensor Shape is a mapping from aggregated-axes to aggregated-maps, which contain axes sizes.
-- Each mapping in a tensor shape can be labelled or unlabelled.
--
-- - A labelled mapping contains the name for an aggregated-axis ('Label'),
-- an 'RClassIdentifier', and a 'MapIdentifier'.
-- - An unlabelled mapping contains only an 'RClassIdentifier' (which acts as the aggregated-axis name) and a 'MapIdentifier'.
data TensorShape = TensorShape
  { labelled :: HM.HashMap Label (RClassIdentifier, MapIdentifier),
    unlabelled :: HM.HashMap RClassIdentifier MapIdentifier
  }
  deriving (Show, Generic)

instance Eq TensorShape where
  (TensorShape l1 u1) == (TensorShape l2 u2) = l1 == l2 && u1 == u2

instance Hashable TensorShape where
  hashWithSalt salt (TensorShape labelled unlabelled) =
    salt
      `hashWithSalt` HM.toList labelled
      `hashWithSalt` HM.toList unlabelled

instance PPrint TensorShape where
  pformatPrec n (TensorShape labelled unlabelled) =
    prettyWithConstructor
      n
      "TensorShape"
      [ encloseList "{" "}" "," $
          [ prettyLabelled label rclass map
          | (label, (rclass, map)) <- HM.toList labelled
          ]
            ++ [ prettyUnlabelled rclass map
               | (rclass, map) <- HM.toList unlabelled
               ]
      ]
    where
      prettyLabelled label rclass map =
        pformat rclass <> " -> " <> pformat map <> " @@ " <> pformat label
      prettyUnlabelled rclass map = pformat rclass <> " -> " <> pformat map

data PartialTensorShapeDesc
  = PartialTensorShapeDesc RClassIdentifier MapIdentifier

-- | A 'TensorShapeDesc' describes a mapping in a tensor shape.
-- It has two constructors:
--
-- - 'UnlabelledDesc': @'RClassIdentifier' 'TensorRight.Internal.DSL.Syntax.-->' 'MapIdentifier'@ can be used to create an unlabelled mapping.
-- - 'LabelledDesc': @'RClassIdentifier' 'TensorRight.Internal.DSL.Syntax.-->' 'MapIdentifier' 'TensorRight.Internal.DSL.Syntax.@@' 'Label'@ can be used to create a labelled mapping.
data TensorShapeDesc
  = UnlabelledDesc RClassIdentifier MapIdentifier
  | LabelledDesc Label RClassIdentifier MapIdentifier

instance ArrowSyntax RClassIdentifier MapIdentifier PartialTensorShapeDesc where
  (-->) = PartialTensorShapeDesc

instance ArrowSyntax RClassIdentifier MapIdentifier TensorShapeDesc where
  (-->) = UnlabelledDesc

instance AtSyntax PartialTensorShapeDesc Label TensorShapeDesc where
  PartialTensorShapeDesc rclass map @@ label = LabelledDesc label rclass map

getTensorShape' ::
  (MonadError Error m) => [TensorShapeDesc] -> m TensorShape
getTensorShape' [] = return $ TensorShape HM.empty HM.empty
getTensorShape' (UnlabelledDesc rclass map : rest) = do
  TensorShape labelled unlabelled <- getTensorShape' rest
  when (HM.member rclass unlabelled) $ throwError "Duplicate rclass without labels"
  return $
    TensorShape labelled (HM.insert rclass map unlabelled)
getTensorShape' (LabelledDesc label rclass map : rest) = do
  TensorShape labelled unlabelled <- getTensorShape' rest
  when (HM.member label labelled) $ throwError "Duplicate label"
  when (HM.member rclass unlabelled) $
    throwError "Labelled rclass already present as unlabelled"
  return $ TensorShape (HM.insert label (rclass, map) labelled) unlabelled

-- | A function to convert a list of 'TensorShapeDesc' to a t'TensorShape'
-- The function makes the following checks:
--
-- - No two unlabelled mappings can have the same 'RClassIdentifier'.
-- - No two labelled mappings can have the same 'Label'.
-- - A labelled mapping cannot have the same 'RClassIdentifier' as an unlabelled mapping.
getTensorShape ::
  (MonadError Error m) => [TensorShapeDesc] -> m TensorShape
getTensorShape descs =
  getTensorShape' $
    sortBy
      ( \a b ->
          case (a, b) of
            (LabelledDesc {}, UnlabelledDesc {}) -> LT
            (UnlabelledDesc {}, LabelledDesc {}) -> GT
            _ -> EQ
      )
      descs

class TensorShapeLike a where
  toTensorShape :: (MonadError Error m) => a -> m TensorShape

instance TensorShapeLike TensorShape where
  toTensorShape :: (MonadError Error m) => TensorShape -> m TensorShape
  toTensorShape = return

instance TensorShapeLike [TensorShapeDesc] where
  toTensorShape = getTensorShape

-- | Represents a t'TensorShape' without any 'MapIdentifier' information.
data AbstractShape = AbstractShape
  { labelled :: HM.HashMap Label RClassIdentifier,
    unlabelled :: HS.HashSet RClassIdentifier
  }
  deriving (Show)

instance Eq AbstractShape where
  (AbstractShape l1 u1) == (AbstractShape l2 u2) = l1 == l2 && u1 == u2

instance PPrint AbstractShape where
  pformatPrec n (AbstractShape labelled unlabelled) =
    prettyWithConstructor
      n
      "AbstractShape"
      [ encloseList "{" "}" "," $
          [prettyLabelled label rclass | (label, rclass) <- HM.toList labelled]
            ++ [pformat rclass | rclass <- HS.toList unlabelled]
      ]
    where
      prettyLabelled label rclass = pformat rclass <> " @@ " <> pformat label

-- | Converts a t'TensorShape' to an t'AbstractShape'
toAbstractShape :: TensorShape -> AbstractShape
toAbstractShape (TensorShape labelled unlabelled) =
  AbstractShape
    { labelled = HM.map fst labelled,
      unlabelled = HM.keysSet unlabelled
    }

-- | Returns all 'RClassRef's in an t'AbstractShape'
abstractShapeAllRefs :: AbstractShape -> HS.HashSet RClassRef
abstractShapeAllRefs (AbstractShape labelled unlabelled) =
  HS.map ByRClass unlabelled `HS.union` HS.map ByLabel (HM.keysSet labelled)

-- | Removes an 'RClassRef' from an t'AbstractShape'
removeRClass ::
  (MonadError T.Text m, TryMerge m) =>
  AbstractShape ->
  RClassRef ->
  m AbstractShape
removeRClass AbstractShape {..} (ByRClass rclass) = do
  assert "RClass not exist" $ HS.member rclass unlabelled
  return $ AbstractShape labelled (HS.delete rclass unlabelled)
removeRClass AbstractShape {..} (ByLabel label) = do
  assert "Label not exist" $ HM.member label labelled
  return $ AbstractShape (HM.delete label labelled) unlabelled

-- | Returns the 'RClassIdentifier' corresponding to an 'RClassRef' given an t'AbstractShape'
getRClassByRClassRef ::
  (MonadError T.Text m, TryMerge m) =>
  AbstractShape ->
  RClassRef ->
  m RClassIdentifier
getRClassByRClassRef AbstractShape {..} (ByRClass rclass) = do
  assert "RClass not exist" $ HS.member rclass unlabelled
  return rclass
getRClassByRClassRef AbstractShape {..} (ByLabel label) =
  case HM.lookup label labelled of
    Nothing -> throwError "Label not exist"
    Just rclass -> return rclass

-- | Adds an 'RClassRef' to an t'AbstractShape'
addRClassByRClassRef ::
  (MonadError T.Text m, TryMerge m) =>
  AbstractShape ->
  RClassRef ->
  RClassIdentifier ->
  m AbstractShape
addRClassByRClassRef AbstractShape {..} (ByRClass rclass) rclass' = do
  assert "RClass already exist" $ not $ HS.member rclass unlabelled
  assert "If adding by rclass itself, then rclass must be the same" $ rclass == rclass'
  return $ AbstractShape labelled (HS.insert rclass' unlabelled)
addRClassByRClassRef AbstractShape {..} (ByLabel label) rclass = do
  assert "Label already exist" $ not $ HM.member label labelled
  return $ AbstractShape (HM.insert label rclass labelled) unlabelled

-- | Concatenates two t'AbstractShape's.
-- The function makes the following checks:
--
-- - The input t'AbstractShape's must not have any overlapping labelled RClass.
-- - The input t'AbstractShape's must not have any overlapping unlabelled RClass.
-- - The resulting t'AbstractShape' must not have any labelled RClass that overlaps with an unlabelled RClass.
concatAbstractShape ::
  (MonadError T.Text m, TryMerge m) =>
  AbstractShape ->
  AbstractShape ->
  m AbstractShape
concatAbstractShape
  (AbstractShape l1 u1)
  (AbstractShape l2 u2) = do
    assert "Labelled rclass overlap" $ HM.null $ HM.intersection l1 l2
    assert "Unlabelled rclass overlap" $ HS.null $ HS.intersection u1 u2
    let newUnlabelledRClasses = u1 `HS.union` u2
    let newLabelled = l1 `HM.union` l2
    let newLabelledRClasses = HS.fromList $ HM.elems newLabelled
    assert "Labelled rclass overlap with unlabelled" $
      HS.null $
        HS.intersection newUnlabelledRClasses newLabelledRClasses
    let newAbstractShape =
          AbstractShape
            (l1 `HM.union` l2)
            (u1 `HS.union` u2)
    return newAbstractShape

-- | Restricts an t'AbstractShape' to the specified set of 'RClassRef's.
restrictAbstractShape ::
  (MonadError T.Text m, TryMerge m) =>
  AbstractShape ->
  RClassRefSet ->
  m AbstractShape
restrictAbstractShape AbstractShape {..} rclasses = do
  let newLabelled =
        HM.filterWithKey (\k _ -> k `HS.member` byLabel) labelled
  let newUnlabelled = HS.intersection unlabelled byRClass
  assert "restrictAbstractShape: some label does not exist" $
    HS.size byLabel == HM.size newLabelled
  assert "restrictAbstractShape: some rclass does not exist" $
    HS.size byRClass == HS.size newUnlabelled
  return $ AbstractShape newLabelled newUnlabelled
  where
    byLabel' [] = []
    byLabel' (ByLabel label : as) = label : byLabel' as
    byLabel' (_ : as) = byLabel' as
    byLabel = HS.fromList $ byLabel' $ HS.toList rclasses

    byRClass' [] = []
    byRClass' (ByRClass rclass : as) = rclass : byRClass' as
    byRClass' (_ : as) = byRClass' as
    byRClass = HS.fromList $ byRClass' $ HS.toList rclasses
