{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module TensorRight.Internal.DSL.Expr
  ( DType (..),
    Params,
    NumTensorAssumption (..),
    ExprDescription (..),
    PaddingArgsExpr (..),
    ConvConfigArgsExpr (..),
    ConvPaddingArgsExpr (..),
    SliceArgsExpr (..),
    DySliceArgsExpr (..),
    UExpr (..),
    Expr (..),
    Env (..),
    DSLContext,
    Rewrite (..),
    runDSLContext,
    evalDSLContext,
    exprId,
    internWithCheck,
    internExpr,
    checkMapHasRClass,
    checkParamsWellFormed,
    validTensorShape,
    monitorExprOnFailure,
    monitorMapOnFailure,
    getRClassByMap,
    rewrite,
  )
where

import Control.Monad (unless)
import Control.Monad.Error.Class (MonadError (throwError))
import Control.Monad.State (MonadState (get, put), StateT (runStateT), evalStateT)
import Data.Function (on)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Hashable (Hashable (hashWithSalt))
import qualified Data.Text as T
import GHC.Generics (Generic)
import Grisette
  ( Default (Default),
    Mergeable (rootStrategy),
    MergingStrategy (NoStrategy),
    PPrint (pformat, pformatPrec),
    SymBool,
    TryMerge,
    viaShow,
  )
import Prettyprinter (Doc, (<+>))
import TensorRight.Internal.Core.Tensor
  ( BoolBinOp (And, Or),
    DType (IntType),
    Elem,
    NumBinOp (Add, Div, Max, Min, Mul, Rem, Sub),
  )
import TensorRight.Internal.Core.Tensor.TensorInt (IsTensorNum, TensorNum)
import TensorRight.Internal.Core.Tensor.Typed
  ( BoolUnaryOp,
    CompareOp (Eqv, Ge, Gt, Le, Lt, Ne),
    NumUnaryOp,
  )
import TensorRight.Internal.DSL.Condition (Condition)
import TensorRight.Internal.DSL.Identifier
  ( MapIdentifier,
    RClassIdentifier,
    TensorIdentifier,
  )
import TensorRight.Internal.DSL.Shape
  ( AbstractShape,
    RClassRef,
    TensorShape (TensorShape, labelled, unlabelled),
    getRClassByRClassRef,
  )
import TensorRight.Internal.Util.Error (Error)
import TensorRight.Internal.Util.Pretty (gprettyParen, prettyWithConstructor)

-- | Internal representation of operator parameters/attributes.
type Params = HM.HashMap RClassRef MapIdentifier

data PaddingArgsExpr = PaddingArgsExpr
  { low :: Params,
    interior :: Params,
    high :: Params
  }
  deriving (Generic, Eq, Show)
  deriving (Hashable)
  deriving (PPrint) via (Default PaddingArgsExpr)

data ConvConfigArgsExpr = ConvConfigArgsExpr
  { batchRClasses :: [RClassRef],
    featureRClasses :: [RClassRef],
    outputFeatureRClasses :: [RClassRef],
    strides :: Params,
    contractingSIMaps :: Params
  }
  deriving (Generic, Eq, Show)
  deriving (Hashable)
  deriving (PPrint) via (Default ConvConfigArgsExpr)

data ConvPaddingArgsExpr = ConvPaddingArgsExpr
  { low :: Params,
    ldilation :: Params,
    high :: Params,
    rdilation :: Params
  }
  deriving (Generic, Eq, Show)
  deriving (Hashable)
  deriving (PPrint) via (Default ConvPaddingArgsExpr)

data SliceArgsExpr = SliceArgsExpr
  { start :: Params,
    end :: Params,
    strides :: Params
  }
  deriving (Generic, Eq, Show)
  deriving (Hashable)
  deriving (PPrint) via (Default SliceArgsExpr)

data DySliceArgsExpr = DySliceArgsExpr
  { start :: Params,
    sizes :: Params
  }
  deriving (Generic, Eq, Show)
  deriving (Hashable)
  deriving (PPrint) via (Default DySliceArgsExpr)

data ExprDescription
  = VarDescription {_identifier :: TensorIdentifier}
  | NumBinOpDescription {_iop :: NumBinOp, _lhs :: Int, _rhs :: Int}
  | NumScalarBinOpDescription
      { _iop :: NumBinOp,
        _lhs :: Int,
        _rhsNum :: Elem
      }
  | BoolBinOpDescription {_bop :: BoolBinOp, _lhs :: Int, _rhs :: Int}
  | BoolScalarBinOpDescription
      { _bop :: BoolBinOp,
        _lhs :: Int,
        _rhsBool :: SymBool
      }
  | CompareOpDescription {_cop :: CompareOp, _lhs :: Int, _rhs :: Int}
  | NumUnaryOpDescription {_iuop :: NumUnaryOp, _expr :: Int}
  | BoolUnaryOpDescription {_buop :: BoolUnaryOp, _expr :: Int}
  | ReduceDescription
      { _expr :: Int,
        _siMaps :: Params
      }
  | BroadcastDescription
      { _expr :: Int,
        _extendedShape :: TensorShape
      }
  | ConstantDescription {_elem :: Elem, _shape :: TensorShape}
  | IotaDescription {_shape :: TensorShape, _axis :: RClassRef}
  | SliceDescription
      { _expr :: Int,
        _slice :: SliceArgsExpr
      }
  | PadDescription
      { _expr :: Int,
        _padElem :: Elem,
        _padding :: PaddingArgsExpr
      }
  | PadLowDescription
      { _expr :: Int,
        _padElem :: Elem,
        _lowPadding :: Params
      }
  | DynamicSliceDescription
      { _expr :: Int,
        _dySlice :: DySliceArgsExpr
      }
  | DynamicUpdateSliceDescription
      { _expr :: Int,
        _update :: Int,
        _start :: Params
      }
  | ConcatDescription {_lhs :: Int, _rhs :: Int, _axis :: RClassRef}
  | ConcatListDescription {_exprs :: [Int], _axis :: RClassRef}
  | RelabelDescription {_expr :: Int, _relabelMap :: HM.HashMap RClassRef RClassRef}
  | DotDescription
      { _lhs :: Int,
        _rhs :: Int,
        _constractionSIMaps :: HM.HashMap RClassRef MapIdentifier,
        _batchRClasses :: [RClassRef]
      }
  | ConvBaseDescription
      { _input :: Int,
        _weight :: Int,
        _convConfig :: ConvConfigArgsExpr
      }
  | ConvDescription
      { _input :: Int,
        _weight :: Int,
        _convConfig :: ConvConfigArgsExpr,
        _convPadding :: ConvPaddingArgsExpr
      }
  | ClampDescription {_min :: Int, _expr :: Int, _max :: Int}
  | ClampScalarDescription
      { _imin :: Elem,
        _expr :: Int,
        _imax :: Elem
      }
  | ReverseTensorDescription {_expr :: Int, _axes :: [RClassRef]}
  | SelectDescription {_cond :: Int, _true :: Int, _false :: Int}
  | ReshapeDegenerateDescription
      { _expr :: Int,
        _introAxes :: [(RClassRef, RClassIdentifier)],
        _elimAxes :: [RClassRef]
      }
  deriving (Generic, Eq, Show)
  deriving (Hashable)
  deriving (PPrint) via (Default ExprDescription)

data UExpr
  = UVar {_identifier :: TensorIdentifier}
  | UNumBinOp {_iop :: NumBinOp, _lhs :: Expr, _rhs :: Expr}
  | UNumScalarBinOp {_iop :: NumBinOp, _lhs :: Expr, _rhsNum :: Elem}
  | UBoolBinOp {_bop :: BoolBinOp, _lhs :: Expr, _rhs :: Expr}
  | UBoolScalarBinOp {_bop :: BoolBinOp, _lhs :: Expr, _rhsBool :: SymBool}
  | UCompareOp {_cop :: CompareOp, _lhs :: Expr, _rhs :: Expr}
  | UNumUnaryOp {_iuop :: NumUnaryOp, _expr :: Expr}
  | UBoolUnaryOp {_buop :: BoolUnaryOp, _expr :: Expr}
  | UReduce {_expr :: Expr, _sikeys :: HM.HashMap RClassRef MapIdentifier}
  | UBroadcast {_expr :: Expr, _extendedShape :: TensorShape}
  | UConstant {_elem :: Elem, _shape :: TensorShape}
  | UIota {_shape :: TensorShape, _axis :: RClassRef}
  | USlice {_expr :: Expr, _slice :: SliceArgsExpr}
  | UPad
      { _expr :: Expr,
        _padElem :: Elem,
        _padding :: PaddingArgsExpr
      }
  | UPadLow
      { _expr :: Expr,
        _padElem :: Elem,
        _lowPadding :: Params
      }
  | UDynamicSlice {_expr :: Expr, _dySlice :: DySliceArgsExpr}
  | UDynamicUpdateSlice {_expr :: Expr, _update :: Expr, _start :: Params}
  | UConcat {_lhs :: Expr, _rhs :: Expr, _axis :: RClassRef}
  | UConcatList {_exprs :: [Expr], _axis :: RClassRef}
  | URelabel {_expr :: Expr, _relabelMap :: HM.HashMap RClassRef RClassRef}
  | UDot
      { _lhs :: Expr,
        _rhs :: Expr,
        _constractionSIMaps :: HM.HashMap RClassRef MapIdentifier,
        _batchRClasses :: [RClassRef]
      }
  | UConvBase
      { _input :: Expr,
        _weight :: Expr,
        _convConfig :: ConvConfigArgsExpr
      }
  | UConv
      { _input :: Expr,
        _weight :: Expr,
        _convConfig :: ConvConfigArgsExpr,
        _convPadding :: ConvPaddingArgsExpr
      }
  | UClamp {_min :: Expr, _expr :: Expr, _max :: Expr}
  | UClampScalar
      { _imin :: Elem,
        _expr :: Expr,
        _imax :: Elem
      }
  | UReverseTensor {_expr :: Expr, _axes :: [RClassRef]}
  | USelect {_cond :: Expr, _true :: Expr, _false :: Expr}
  | UReshapeDegenerate
      { _expr :: Expr,
        _introAxes :: [(RClassRef, RClassIdentifier)],
        _elimAxes :: [RClassRef]
      }

describe :: UExpr -> ExprDescription
describe (UVar i) = VarDescription i
describe (UNumBinOp o l r) = NumBinOpDescription o (_id l) (_id r)
describe (UNumScalarBinOp o l r) = NumScalarBinOpDescription o (_id l) r
describe (UBoolBinOp o l r) = BoolBinOpDescription o (_id l) (_id r)
describe (UBoolScalarBinOp o l r) = BoolScalarBinOpDescription o (_id l) r
describe (UCompareOp o l r) = CompareOpDescription o (_id l) (_id r)
describe (UNumUnaryOp o e) = NumUnaryOpDescription o (_id e)
describe (UBoolUnaryOp o e) = BoolUnaryOpDescription o (_id e)
describe (UReduce e si) = ReduceDescription (_id e) si
describe (UBroadcast e si) = BroadcastDescription (_id e) si
describe (UConstant e s) = ConstantDescription e s
describe (UIota s d) = IotaDescription s d
describe (USlice e s) = SliceDescription (_id e) s
describe (UPad e v c) = PadDescription (_id e) v c
describe (UPadLow e v c) = PadLowDescription (_id e) v c
describe (UDynamicSlice e s) = DynamicSliceDescription (_id e) s
describe (UDynamicUpdateSlice e u s) = DynamicUpdateSliceDescription (_id e) (_id u) s
describe (UConcat l r d) = ConcatDescription (_id l) (_id r) d
describe (UConcatList ts d) = ConcatListDescription (map _id ts) d
describe (URelabel e m) = RelabelDescription (_id e) m
describe (UDot l r c b) = DotDescription (_id l) (_id r) c b
describe (UConvBase i w c) = ConvBaseDescription (_id i) (_id w) c
describe (UConv i w c p) = ConvDescription (_id i) (_id w) c p
describe (UClamp mi e ma) = ClampDescription (_id mi) (_id e) (_id ma)
describe (UClampScalar mi e ma) = ClampScalarDescription mi (_id e) ma
describe (UReverseTensor e a) = ReverseTensorDescription (_id e) a
describe (USelect c t f) = SelectDescription (_id c) (_id t) (_id f)
describe (UReshapeDegenerate e i o) = ReshapeDegenerateDescription (_id e) i o

data Expr
  = Var {_id :: Int, _identifier :: TensorIdentifier}
  | NumBinOp {_id :: Int, _iop :: NumBinOp, _lhs :: Expr, _rhs :: Expr}
  | NumScalarBinOp
      { _id :: Int,
        _iop :: NumBinOp,
        _lhs :: Expr,
        _rhsNum :: Elem
      }
  | BoolBinOp {_id :: Int, _bop :: BoolBinOp, _lhs :: Expr, _rhs :: Expr}
  | BoolScalarBinOp
      { _id :: Int,
        _bop :: BoolBinOp,
        _lhs :: Expr,
        _rhsBool :: SymBool
      }
  | CompareOp {_id :: Int, _cop :: CompareOp, _lhs :: Expr, _rhs :: Expr}
  | NumUnaryOp {_id :: Int, _iuop :: NumUnaryOp, _expr :: Expr}
  | BoolUnaryOp {_id :: Int, _buop :: BoolUnaryOp, _expr :: Expr}
  | Reduce
      { _id :: Int,
        _expr :: Expr,
        _sikeys :: HM.HashMap RClassRef MapIdentifier
      }
  | Broadcast {_id :: Int, _expr :: Expr, _extendedShape :: TensorShape}
  | Constant {_id :: Int, _elem :: Elem, _shape :: TensorShape}
  | Iota {_id :: Int, _shape :: TensorShape, _axis :: RClassRef}
  | Slice
      { _id :: Int,
        _expr :: Expr,
        _slice :: SliceArgsExpr
      }
  | Pad
      { _id :: Int,
        _expr :: Expr,
        _padElem :: Elem,
        _padding :: PaddingArgsExpr
      }
  | PadLow
      { _id :: Int,
        _expr :: Expr,
        _padElem :: Elem,
        _lowPadding :: Params
      }
  | DynamicSlice
      { _id :: Int,
        _expr :: Expr,
        _dySlice :: DySliceArgsExpr
      }
  | DynamicUpdateSlice
      { _id :: Int,
        _expr :: Expr,
        _update :: Expr,
        _start :: Params
      }
  | Concat {_id :: Int, _lhs :: Expr, _rhs :: Expr, _axis :: RClassRef}
  | ConcatList {_id :: Int, _exprs :: [Expr], _axis :: RClassRef}
  | Relabel
      { _id :: Int,
        _expr :: Expr,
        _relabelMap :: HM.HashMap RClassRef RClassRef
      }
  | Dot
      { _id :: Int,
        _lhs :: Expr,
        _rhs :: Expr,
        _constractionSIMaps :: HM.HashMap RClassRef MapIdentifier,
        _batchRClasses :: [RClassRef]
      }
  | ConvBase
      { _id :: Int,
        _input :: Expr,
        _weight :: Expr,
        _convConfig :: ConvConfigArgsExpr
      }
  | Conv
      { _id :: Int,
        _input :: Expr,
        _weight :: Expr,
        _convConfig :: ConvConfigArgsExpr,
        _convPadding :: ConvPaddingArgsExpr
      }
  | Clamp {_id :: Int, _min :: Expr, _expr :: Expr, _max :: Expr}
  | ClampScalar
      { _id :: Int,
        _imin :: Elem,
        _expr :: Expr,
        _imax :: Elem
      }
  | ReverseTensor {_id :: Int, _expr :: Expr, _axes :: [RClassRef]}
  | Select {_id :: Int, _cond :: Expr, _true :: Expr, _false :: Expr}
  | ReshapeDegenerate
      { _id :: Int,
        _expr :: Expr,
        _introAxes :: [(RClassRef, RClassIdentifier)],
        _elimAxes :: [RClassRef]
      }
  deriving (Show)

exprId :: Expr -> Int
exprId = _id

infixPrettyNumBinOp :: NumBinOp -> Doc ann
infixPrettyNumBinOp Add = "+"
infixPrettyNumBinOp Sub = "-"
infixPrettyNumBinOp Mul = "*"
infixPrettyNumBinOp Max = "`max`"
infixPrettyNumBinOp Min = "`min`"
infixPrettyNumBinOp Div = "/"
infixPrettyNumBinOp Rem = "%"

infixNumBinOpPrec :: NumBinOp -> Int
infixNumBinOpPrec Add = 6
infixNumBinOpPrec Sub = 6
infixNumBinOpPrec Mul = 7
infixNumBinOpPrec Max = 10
infixNumBinOpPrec Min = 10
infixNumBinOpPrec Div = 7
infixNumBinOpPrec Rem = 7

infixPrettyBoolBinOp :: BoolBinOp -> Doc ann
infixPrettyBoolBinOp Or = "||"
infixPrettyBoolBinOp And = "&&"

infixBoolBinOpPrec :: BoolBinOp -> Int
infixBoolBinOpPrec Or = 2
infixBoolBinOpPrec And = 3

infixPrettyCompareOp :: CompareOp -> Doc ann
infixPrettyCompareOp Lt = "<"
infixPrettyCompareOp Le = "<="
infixPrettyCompareOp Eqv = "=="
infixPrettyCompareOp Ne = "/="
infixPrettyCompareOp Gt = ">"
infixPrettyCompareOp Ge = ">="

infixCompareOpPrec :: CompareOp -> Int
infixCompareOpPrec _ = 4

instance PPrint Expr where
  pformatPrec n (Var _ i) = pformatPrec n i
  pformatPrec n (NumBinOp _ o l r) =
    gprettyParen (n > infixNumBinOpPrec o) $
      pformatPrec (infixNumBinOpPrec o) l
        <+> infixPrettyNumBinOp o
        <+> pformatPrec (infixNumBinOpPrec o + 1) r
  pformatPrec n (NumScalarBinOp _ o l r) =
    gprettyParen (n > infixNumBinOpPrec o) $
      pformatPrec (infixNumBinOpPrec o) l
        <+> infixPrettyNumBinOp o
        <+> pformatPrec (infixNumBinOpPrec o + 1) r
  pformatPrec n (BoolBinOp _ o l r) =
    gprettyParen (n > infixBoolBinOpPrec o) $
      pformatPrec (infixBoolBinOpPrec o) l
        <+> infixPrettyBoolBinOp o
        <+> pformatPrec (infixBoolBinOpPrec o + 1) r
  pformatPrec n (BoolScalarBinOp _ o l r) =
    gprettyParen (n > infixBoolBinOpPrec o) $
      pformatPrec (infixBoolBinOpPrec o) l
        <+> infixPrettyBoolBinOp o
        <+> pformatPrec (infixBoolBinOpPrec o + 1) r
  pformatPrec n (CompareOp _ o l r) =
    gprettyParen (n > infixCompareOpPrec o) $
      pformatPrec (infixCompareOpPrec o) l
        <+> infixPrettyCompareOp o
        <+> pformatPrec (infixCompareOpPrec o + 1) r
  pformatPrec n (NumUnaryOp _ o e) =
    prettyWithConstructor n (pformatPrec 11 o) [pformatPrec 11 e]
  pformatPrec n (BoolUnaryOp _ o e) =
    prettyWithConstructor n (pformatPrec 11 o) [pformatPrec 11 e]
  pformatPrec n (Reduce _ e si) =
    prettyWithConstructor n "reduce" [pformatPrec 11 e, pformatPrec 11 si]
  pformatPrec n (Broadcast _ e si) =
    prettyWithConstructor n "broadcast" [pformatPrec 11 e, pformatPrec 11 si]
  pformatPrec n (Constant _ i s) =
    prettyWithConstructor n "constant" [pformatPrec 11 i, pformatPrec 11 s]
  pformatPrec n (Iota _ s d) =
    prettyWithConstructor n "iota" [pformatPrec 11 s, pformatPrec 11 d]
  pformatPrec n (Slice _ e s) =
    prettyWithConstructor n "slice" [pformatPrec 11 e, pformatPrec 11 s]
  pformatPrec n (Pad _ e v c) =
    prettyWithConstructor n "pad" [pformatPrec 11 e, pformatPrec 11 v, pformatPrec 11 c]
  pformatPrec n (PadLow _ e v c) =
    prettyWithConstructor n "padLow" [pformatPrec 11 e, pformatPrec 11 v, pformatPrec 11 c]
  pformatPrec n (DynamicSlice _ e s) =
    prettyWithConstructor n "dynamicSlice" [pformatPrec 11 e, pformatPrec 11 s]
  pformatPrec n (DynamicUpdateSlice _ e u s) =
    prettyWithConstructor n "dynamicUpdateSlice" [pformatPrec 11 e, pformatPrec 11 u, pformatPrec 11 s]
  pformatPrec n (Concat _ l r d) =
    prettyWithConstructor n "concat" [pformatPrec 11 l, pformatPrec 11 r, pformatPrec 11 d]
  pformatPrec n (ConcatList _ es d) =
    prettyWithConstructor n "concatList" [pformatPrec 11 es, pformatPrec 11 d]
  pformatPrec n (Relabel _ e m) =
    prettyWithConstructor n "relabel" [pformatPrec 11 e, pformatPrec 11 m]
  pformatPrec n (Dot _ l r c b) =
    prettyWithConstructor n "dot" [pformatPrec 11 l, pformatPrec 11 r, pformatPrec 11 c, pformatPrec 11 b]
  pformatPrec n (ConvBase _ i w c) =
    prettyWithConstructor
      n
      "convBase"
      [ "inputs=" <> pformatPrec 11 i,
        "weights=" <> pformatPrec 11 w,
        pformatPrec 11 c
      ]
  pformatPrec n (Conv _ i w c p) =
    prettyWithConstructor
      n
      "conv"
      [ "inputs=" <> pformatPrec 11 i,
        "weights=" <> pformatPrec 11 w,
        pformatPrec 11 c,
        pformatPrec 11 p
      ]
  pformatPrec n (Clamp _ mi e ma) =
    prettyWithConstructor
      n
      "clamp"
      [ "min=" <> pformatPrec 11 mi,
        "t=" <> pformatPrec 11 e,
        "max=" <> pformatPrec 11 ma
      ]
  pformatPrec n (ClampScalar _ mi e ma) =
    prettyWithConstructor
      n
      "clampScalar"
      [ "min=" <> pformatPrec 11 mi,
        "t=" <> pformatPrec 11 e,
        "max=" <> pformatPrec 11 ma
      ]
  pformatPrec n (ReverseTensor _ e a) =
    prettyWithConstructor n "reverseTensor" [pformatPrec 11 e, pformatPrec 11 a]
  pformatPrec n (Select _ c t f) =
    prettyWithConstructor
      n
      "select"
      [pformatPrec 11 c, pformatPrec 11 t, pformatPrec 11 f]
  pformatPrec n (ReshapeDegenerate _ e i o) =
    prettyWithConstructor
      n
      "reshapeDegenerate"
      [pformatPrec 11 e, pformatPrec 11 i, pformatPrec 11 o]

instance Eq Expr where
  (==) = (==) `on` _id

instance Hashable Expr where
  hashWithSalt s e = hashWithSalt s (_id e)

identify :: Int -> UExpr -> Expr
identify i (UVar id) = Var i id
identify i (UNumBinOp l r o) = NumBinOp i l r o
identify i (UNumScalarBinOp l r o) = NumScalarBinOp i l r o
identify i (UBoolBinOp l r o) = BoolBinOp i l r o
identify i (UBoolScalarBinOp l r o) = BoolScalarBinOp i l r o
identify i (UCompareOp l r o) = CompareOp i l r o
identify i (UNumUnaryOp e o) = NumUnaryOp i e o
identify i (UBoolUnaryOp e o) = BoolUnaryOp i e o
identify i (UReduce e si) = Reduce i e si
identify i (UBroadcast e si) = Broadcast i e si
identify i (UConstant e s) = Constant i e s
identify i (UIota s d) = Iota i s d
identify i (USlice e s) = Slice i e s
identify i (UPad e v c) = Pad i e v c
identify i (UPadLow e v c) = PadLow i e v c
identify i (UDynamicSlice e s) = DynamicSlice i e s
identify i (UDynamicUpdateSlice e u s) = DynamicUpdateSlice i e u s
identify i (UConcat l r d) = Concat i l r d
identify i (UConcatList es d) = ConcatList i es d
identify i (URelabel e m) = Relabel i e m
identify i (UDot l r c b) = Dot i l r c b
identify i (UConvBase input w c) = ConvBase i input w c
identify i (UConv input w c p) = Conv i input w c p
identify i (UClamp mi e ma) = Clamp i mi e ma
identify i (UClampScalar mi e ma) = ClampScalar i mi e ma
identify i (UReverseTensor e a) = ReverseTensor i e a
identify i (USelect c t f) = Select i c t f
identify i (UReshapeDegenerate e intro elim) = ReshapeDegenerate i e intro elim

data NumTensorAssumption = NumTensorAssumption
  { tensors :: [Expr],
    forallIndices :: MapIdentifier,
    assumption :: forall v. (IsTensorNum v) => [TensorNum v] -> SymBool
  }

instance Show NumTensorAssumption where
  show NumTensorAssumption {..} =
    "NumTensorAssumption { tensors = "
      <> show tensors
      <> ", forallIndices = "
      <> show forallIndices
      <> " }"

instance PPrint NumTensorAssumption where
  pformat = viaShow

data Env = Env
  { declaredRClasses :: HS.HashSet RClassIdentifier,
    mapRClasses :: HM.HashMap MapIdentifier RClassIdentifier,
    tensorShapes :: HM.HashMap TensorIdentifier TensorShape,
    tensorDTypes :: HM.HashMap TensorIdentifier DType,
    exprs :: HM.HashMap ExprDescription Expr,
    exprAbstractShapes :: HM.HashMap Int AbstractShape,
    exprDTypes :: HM.HashMap Int DType,
    preConditions :: [Condition],
    rankConditions :: HM.HashMap RClassIdentifier Int,
    numTensorAssumptions :: [NumTensorAssumption],
    siMaps :: HS.HashSet MapIdentifier,
    siRelations :: [Condition],
    monitoringExprs :: [(T.Text, Expr)],
    monitoringMaps :: [(T.Text, RClassRef, MapIdentifier)],
    lhsSIMaps :: HS.HashSet MapIdentifier,
    rhsSIMaps :: HS.HashSet MapIdentifier
  }
  deriving (Show, Generic)
  deriving (PPrint) via (Default Env)

instance Mergeable Env where
  rootStrategy = NoStrategy

emptyEnv :: Env
emptyEnv =
  Env
    HS.empty
    HM.empty
    HM.empty
    HM.empty
    HM.empty
    HM.empty
    HM.empty
    []
    HM.empty
    []
    HS.empty
    []
    []
    []
    HS.empty
    HS.empty

-- | The context for the DSL. Your rewriting rule usually should have the type
-- @t'DSLContext' t'Rewrite'@.
newtype DSLContext a = DSLContext {unDSLContext :: StateT Env (Either T.Text) a}
  deriving newtype
    ( Functor,
      Applicative,
      Monad,
      MonadState Env,
      MonadError Error,
      TryMerge
    )

runDSLContext :: DSLContext a -> Either T.Text (a, Env)
runDSLContext ctx = runStateT (unDSLContext ctx) emptyEnv

evalDSLContext :: DSLContext a -> Either T.Text a
evalDSLContext ctx = evalStateT (unDSLContext ctx) emptyEnv

instance MonadFail DSLContext where
  fail = throwError . T.pack

internExpr :: UExpr -> AbstractShape -> DType -> DSLContext Expr
internExpr uexpr shape dtype = do
  env <- get
  let desc = describe uexpr
  let definedExprs = exprs env
  case HM.lookup desc definedExprs of
    Just expr -> return expr
    Nothing -> do
      let exprId = HM.size (exprs env)
      let expr = identify exprId uexpr
      put $
        env
          { exprs = HM.insert (describe uexpr) expr (exprs env),
            exprAbstractShapes =
              HM.insert (_id expr) shape (exprAbstractShapes env),
            exprDTypes = HM.insert (_id expr) dtype (exprDTypes env)
          }
      return expr

internWithCheck :: UExpr -> DSLContext (AbstractShape, DType) -> DSLContext Expr
internWithCheck uexpr check = do
  env <- get
  let desc = describe uexpr
  let definedExprs = exprs env
  case HM.lookup desc definedExprs of
    Just expr -> return expr
    Nothing -> do
      (shape, dtype) <- check
      internExpr uexpr shape dtype

getRClassByMap :: MapIdentifier -> DSLContext RClassIdentifier
getRClassByMap map = do
  Env {..} <- get
  case HM.lookup map mapRClasses of
    Just rclass -> return rclass
    Nothing -> throwError "Map not exist"

checkMapHasRClass :: RClassIdentifier -> MapIdentifier -> DSLContext ()
checkMapHasRClass rclass map = do
  rclass' <- getRClassByMap map
  unless (rclass == rclass') $ throwError "RClass and map mismatch"

-- Env {..} <- get
-- case HM.lookup map mapRClasses of
--   Nothing -> throwError "Map not exist"
--   Just rclass' -> unless (rclass == rclass') $ throwError "RClass and map mismatch"

checkParamsWellFormed ::
  AbstractShape -> HM.HashMap RClassRef MapIdentifier -> DSLContext ()
checkParamsWellFormed shape params = do
  rclassMapList <-
    traverse (\(ref, map) -> (,map) <$> getRClassByRClassRef shape ref) $
      HM.toList params
  mapM_ (uncurry checkMapHasRClass) rclassMapList

validTensorShape :: TensorShape -> DSLContext ()
validTensorShape TensorShape {..} = do
  Env {..} <- get
  let unlabelledRClasses = HM.keysSet unlabelled
  let labelledRClasses = HS.fromList $ fst <$> HM.elems labelled
  let allRClasses = unlabelledRClasses <> labelledRClasses
  unless (HS.isSubsetOf allRClasses declaredRClasses) $
    throwError "RClass not exist, is that created using newRClass/newRClass'?"
  unless (HS.intersection unlabelledRClasses labelledRClasses == HS.empty) $
    throwError "Labelled and unlabelled rclass overlap"
  go mapRClasses $ HM.toList unlabelled
  go mapRClasses $ HM.elems labelled
  where
    go _ [] = return ()
    go mapRClasses ((rclassName, mapName) : ls) = do
      case HM.lookup mapName mapRClasses of
        Nothing ->
          throwError $
            "Map not exist, is that created using "
              <> "newDimMap/newDimMap'?"
        Just rclassName' ->
          unless (rclassName == rclassName') $
            throwError "RClass and map mismatch"
      go mapRClasses ls

-- | Monitor the validity and shape of an expression on failure.
monitorExprOnFailure :: T.Text -> Expr -> DSLContext ()
monitorExprOnFailure msg expr = do
  env <- get
  put $ env {monitoringExprs = (msg, expr) : monitoringExprs env}

-- | Monitor the contents of a map on failure.
monitorMapOnFailure :: T.Text -> RClassRef -> MapIdentifier -> DSLContext ()
monitorMapOnFailure msg ref map = do
  env <- get
  put $ env {monitoringMaps = (msg, ref, map) : monitoringMaps env}

-- | A rewriting rule.
data Rewrite = Rewrite {name :: T.Text, lhs :: Expr, rhs :: Expr}
  deriving (Generic, Eq, Show)
  deriving (PPrint) via (Default Rewrite)

rewrite :: T.Text -> Expr -> Expr -> DSLContext Rewrite
rewrite name lhs rhs = return $ Rewrite name lhs rhs
