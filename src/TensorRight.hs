{-# LANGUAGE DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module TensorRight
  ( -- * TensorRight DSL

    --

    -- | We introduce a domain-specific language (DSL) for specifying tensor
    -- graph rewrites. The DSL contains constructs to define complex tensor
    -- expressions, specify preconditions, define rewrite rules, and verify
    -- them.

    -- * Language contructs

    -- ** @RClasses@

    -- | An @RClass@ represents a set of named axes.
    -- Every @RClass@ can be instantiated to an arbitrary number of individual-axes, and this set is kept uninterpreted/symbolic.
    -- Our language does not allow splitting of an @RClass@ into smaller @RClasses@,
    -- or adding named-axes to an @RClass@. This means that to operate on an
    -- @RClass@, the user needs to perform the same operation on every
    -- named-axis in it.
    --
    -- We can use 'newRClass' and 'newRClasses' to declare @RClasses@ in our language:

    -- | @
    --   rclass <- 'newRClass' "rclass"
    --   [rclass0, rclass1] <- 'newRClasses' ["rclass0", "rclass1"]
    -- @

    -- | This is written using Haskell's @do@ notation. 'newRClass' takes an @RClass@
    -- name and return an @RClass@ identifier corresponding to the @RClass@, while 'newRClasses'
    -- takes a list of @RClass@ names, and returns a list of @RClass@ identifiers,
    -- corresponding to those names. The returned identifiers can be used
    -- further in the code.

    -- ** Maps

    -- | As seen before, an @RClass@ is a symbolic set of named-axes. If we
    -- want to represent the sizes of named-axes in an @RClass@, we can use a
    -- map from those named-axes to their respective sizes.
    -- The domain of the map is the same as the named-axes in the @RClass@.
    -- Since @RClasses@ are symbolic in our DSL and are represented by
    -- identifiers, these maps would also be symbolic and can be represented by identifiers.
    -- The maps can be instantiated to any number of named-axes in the @RClass@.
    --
    -- We can use the 'newMap' and 'newMaps' functions to declare maps on a
    -- given @RClass@ in our language:

    -- | @
    -- map <- 'newMap' "map" rclass
    -- [map1, map2] <- 'newMaps' ["map1, map2"] rclass
    -- @

    -- | 'newMap' takes a Map name and an @RClass@ identifier and returns a
    -- @Map@ identifier, while 'newMaps' takes a list of names and returns a
    -- list of @Map@ identifiers on the given @RClass@. A @Map@ identifier
    -- represents a symbolic map, whose domain is the same as the named-axes in
    -- an @RClass@.
    -- So, we can say in this example, that @dom(map) = rclass@.
    --
    -- The same map structure can also be used to represent operator attributes
    -- like slice strides, padding sizes, etc.

    -- *** Syntactic sugars for creating maps

    -- | Sometimes, we want to create a map with some constraints, like all the
    -- values in the map should be non-negative, or all the values should be
    -- constant. This can be achieved with preconditions (see below), but these
    -- requirements are very common and using preconditions can be verbose. So,
    -- we provide some syntax sugars for creating such maps:

    -- | @
    -- nonNeg <- 'newNonNegMap' "nonNeg" rclass
    -- constMap <- 'newConstMap' "constMap" 1 rclass
    -- @

    -- | In the code, the first line creates a map named @nonNeg@ on the given
    -- @RClass@, with the constraint that all the elements in the map should be
    -- non-negative. The second line creates a map named @constMap@ on the given
    -- rclass with all the elements in the map being constant 1.

    -- | We may also combine multiple maps into a single map, using the
    -- 'combineMap' call:

    -- | @
    -- summedMap <- 'combineMap' "summedMap" 'sum' [map1, map2]
    -- -- 'sumMap' is equivalent to 'combineMap' with 'sum' as the combining function
    -- summedMap <- 'sumMap' "summedMap" [map1, map2]
    -- @
    -- See 'TensorRight.combineMap' for more details.

    -- ** Tensor creation

    -- | To describe a tensor, we need to describe its shape first. A tensor
    -- comprises of a set of @RClasses@, possibly duplicated, where each @RClass@ has
    -- its own set of named-axes. A tensor's shape is supposed to tell the
    -- size of the tensor along every axis. We can describe the shape of a
    -- tensor as follows:
    --
    -- * For each @RClass@, we can use a @Map@ identifier to
    -- represent sizes of the named-axes in that @RClass@
    -- * The shape of tensor can be represented as a nested map from @RClass@ identifiers to @Map@ identifiers.
    --
    -- For example, we can create a tensor having two @RClasses@ @rclass0@ and
    -- @rclass0@ as follows:

    -- | @
    --
    -- [rclass0, rclass1] <- 'newRClasses' ["rclass0", "rclass1"]
    -- size0 <- 'newMap' "size0" rclass0
    -- size1 <- 'newMap' "size1" rclass1
    --
    -- let tensorShape = [rclass0 '-->' size0, rclass1 '-->' size1]
    --
    -- tensor <- 'newTensor' \@'TensorInt' "tensor" tensorShape
    -- @

    -- | We first declared two @RClass@ identifiers @rclass0@ and @rclass1@. Then, we
    -- declared @Map@ identifiers @size0@ and @size2@ on @rclass0@ and @rclass1@
    -- respectively. Then @tensorShape@ represents the shape of a tensor with 2
    -- @RClasses@ and the specified sizes. @rclass0 '-->' size0@ represents that
    -- @size0@ contains the sizes of named-axes in @rclass0@.
    --
    -- We then created a tensor using 'newTensor', which takes a name for the
    -- tensor, the base element type (in this case 'TensorInt') and the tensor
    -- shape. 'newTensor' returns a @Tensor@ identifier, which can be used to
    -- refer to this tensor in expressions. The created tensor is said to
    -- contain symbolic integer elements and is of shape @tensorShape@.

    -- *** Duplicate RClasses

    -- | We could have multiple copies of the same @RClass@ in a tensor's shape. For
    -- example, consider a tensor with 2 copies of @rclass0@

    -- | @
    -- rclass0 <- 'newRClass' "rclass0"
    -- [size, size'] <- 'newMaps' ["size", "size'"] rclass0
    -- let tensorShape = [rclass0 '-->' size, rclass0 '-->' size']
    -- tensor <- 'newTensor' \@'TensorInt' "tensor" tensorShape
    -- @

    -- | In such a case, if @rclass0@ had \(k\) named-axes, then the tensor has
    -- \(2k\) named-axes. Let's say we wanted to operate on this tensor, like
    -- reduce on one specific copy of @rclass0@.

    -- | @
    -- out <- 'reduce' tensor [rclass0 --\> ...]
    -- @

    -- | It is unclear in this expression, which copy of @rclass0@ gets reduced
    -- out -- is it the one with sizes @size@ or @size'@? To mitigate this
    -- issue, we allow the user to diambiguate duplicate @RClasses@ with labels,
    -- and use those labels to refer to a specific @RClass@. We use the '@@'
    -- syntax to specify labels while constructing tensor shapes.
    -- Labels are simply strings.

    -- | @
    -- let tensorShape = [rclass0 '-->' size '@@' "label0", rclass0 '-->' size' '@@' "label1"]
    -- tensor <- 'newTensor' \@'TensorInt' "tensor" tensorShape
    -- out <- 'reduce' tensor [(ByLabel "label1") --\> ...]
    -- @

    -- | Now, this expression is unambiguous and we can specify the @RClass@ to
    -- reduce on by using an 'RClassRef' with the label @label1@.
    --
    -- Note that in a tensor's shapes, if an @RClass@ identifier appears multiple
    -- times, then all copies need to have a disambigutating label.
    -- Some examples are shown below:

    -- | @
    -- let tensorShapeValid =
    --       [
    --         rclass0 '-->' size '@@' "label0",
    --         rclass0 '-->' size' '@@' "label1",
    --         rclass0 '-->' size '@@' "label2"
    --       ]
    -- let tensorShapeInvalid =
    --       [
    --         rclass0 '-->' size '@@' "label0",
    --         rclass0 '-->' size'
    --       ]
    -- @

    -- | @tensorShapeValid@ is a valid shape, since all copies of @rclass0@ have a
    -- label, but the second shape is invalid. For the first shape, the user can
    -- refer to the @RClasses@ by @'ByLabel' "label0"@ for the first copy,
    -- @'ByLabel' "label1"@ for the second copy, and @'ByLabel' "label2"@
    -- for the third copy.

    -- | The user can omit labels in the case when no disambiguatation is needed.

    -- | @
    -- let tensorShapeValid =
    --       [
    --         rclass0 '-->' size0 '@@' "label0",
    --         rclass1 '-->' size1 '@@' "label1"
    --       ]
    -- let tensorShapeValid' =
    --       [
    --         rclass0 '-->' size0 '@@' "label0",
    --         rclass1 '-->' size1
    --       ]
    -- let tensorShapeValid'' =
    --       [
    --         rclass0 '-->' size0,
    --         rclass1 '-->' size1
    --       ]
    -- @

    -- | All of these shapes are valid, but the only difference is that we need
    -- to use the label @label1@ to refer to @rclass1@ in the first shape (using 'ByLabel'), while
    -- in the second and third shape, we need to refer to it by @rclass1@ itself (using 'ByRClass'). Note that
    -- there was no need to specify labels here, because there are no duplicate
    -- @RClasses@, but we allow the user the flexibility to use labels.

    -- ** Tensor expressions

    -- | We will now describe the tensor operations supported in our DSL. @'Expr'@
    -- represents the type of a tensor expression. Refer to
    -- <https://github.com/ADAPT-uiuc/TensorRight/tree/master/rules>
    -- to take a look at concrete examples on how to instantiate tensor
    -- expressions.

    -- | For example, you may construct a tensor expression as follows:

    -- | @
    -- rclass <- 'newRClass' "rclass"
    -- map <- 'newMap' "map" rclass
    -- tensor <- 'newTensor' \@'TensorInt' "tensor" [rclass --\> map]
    -- expr <- 'numBinOp' 'Add' tensor tensor
    -- @

    -- | For the detailed list of operations supported, refer to the
    -- [operations]("TensorRight#g:op") section.

    -- ** Rewrite rules

    -- | A Rewrite rule consists of
    --
    -- * An LHS Tensor Expression
    -- * An RHS Tensor Expression
    -- * A set of preconditions (optional)
    -- * A set of si-relations (optional)
    --
    -- We saw in the previous section how we can construct tensor expressions.
    -- We will now look at contructs to specify preconditions, si-relations and
    -- rewrite rules.

    -- *** Preconditions

    -- | Preconditions are boolean (or symbolic boolean) valued conditions,
    -- under which the rewrite rule is supposedly correct. We can specify
    -- preconditions using the 'precondition' function. Its syntax is

    -- | @
    -- 'precondition' [m1, m2, ...] f
    -- @

    -- | where
    --
    -- * @[m1, m2, ...]@ is a list of @Map@ identifiers, all previously declared.
    --   It contains all the maps over which the precondition is
    --   defined
    -- * @f :: ['Grisette.SymInteger'] -> 'Grisette.SymBool'@ is a function, that takes a list of
    --   symbolic integers, and returns a symbolic boolean. The condition will
    --   be applied to each group of the elements with the same axes and
    --   combined with a logical AND to get the final symbolic boolean.
    --
    -- For example, we can write a precondition expressing that a maps needs to
    -- have all values as 0:

    -- | @
    -- rclass <- 'newRClass' "rclass"
    -- [size, padSize] <- 'newMap' ["size", "padSize"] rclass
    -- tensor <- 'newTensor' \@'TensorInt' "t" [rclass --\> size]
    -- lhs <- 'pad' tensor ('intElem' 0) $
    --   v'Padding'
    --     { low = [rclass '-->' padSize],
    --       interior = [rclass '-->' padSize],
    --       high = [rclass '-->' padSize]
    --     }
    -- 'precondition' [padSize] $ \[p] -> p .== 0
    -- @

    -- | The precondition first takes a list, containing only the @Map@ identifier
    -- @padSize@. It then takes a function, whose only argument is a
    -- singleton list containing the symbolic padding size and check if the
    -- value is 0 or not. This function is applied to every axis in the map,
    -- and the final result checks if all values in @padSize@ are 0 or not.
    --
    -- The user can add multiple preconditions by using multiple calls to
    -- 'precondition'. The semantics are that the final precondition is the
    -- conjunction of all the individual preconditions.
    --
    -- For the constructs available to the user to express preconditions, please
    -- refer to the [preconditions]("TensorRight#g:precond") section and
    -- functions 'TensorRight.precondition', 'TensorRight.precondition''.
    --
    -- Apart from the helpers provided there, some Grisette operators are also
    -- useful, like 'Grisette..==', 'Grisette.symIte', etc.

    -- *** SI-relations

    -- | The syntax to add si-relations is similar to preconditions -- we just
    -- need to use 'siRelation' instead of 'precondition'. For example, this
    -- si-relation expresses that rclass0lhssi == rclass0rhssi:

    -- | @
    -- 'siRelation' [rclass0lhssi, rclass0rhssi] $
    --   \[l, r] -> l .== r
    -- @
    -- Once all si-relations are declared, the user needs to call 'checkSIMap'
    -- and pass the list of all LHS si-maps and the list of all RHS si-maps.
    -- This tells TensorRight which @Map@ identifiers are si-maps.

    -- *** Rewrite rules

    -- | Once we have declared all @RClasses@, @Maps@,
    -- @Tensors@, created expressions and added preconditions, we can
    -- use the v'Rewrite' constructor to create a rewrite rule:

    -- | @
    -- lhs <- ...
    -- rhs <- ...
    -- return $
    --   v'Rewrite' "lhs => rhs" lhs rhs
    -- @

    -- | Here is a full example, that creates a rewrite rule, and wraps it in
    -- the appropriate context.

    -- | @
    -- rule :: 'DSLContext' t'Rewrite'
    -- rule = do
    --   rclass <- 'newRClass' "rclass"
    --   map <- 'newMap' "map" rclass
    --
    --   tensor <- 'newTensor' \@'TensorInt' "tensor" [rclass --\> map]
    --
    --   constTensor1 <- 'constant' \@'TensorInt' "a" [rclass --\> map]
    --   constTensor2 <- 'constant' \@'TensorInt' "b" [rclass --\> map]
    --   lhs <- 'numBinOp' 'Add' ('numBinOp' 'Add' tensor constTensor1) constTensor2
    --   rhs <- 'numBinOp' 'Add' tensor ('numBinOp' 'Add' constTensor1 constTensor2)
    --
    --   return $
    --     v'Rewrite' "Add(Add(A, Const), Const2) ⇒ Add(A, Add(Const, Const2))" lhs rhs
    -- @

    -- | Once this rule is declared, we can verify it using 'verifyDSL'.

    -- | @
    -- main :: IO ()
    -- main = 'verifyDSL' rule
    -- @

    -- ** Verification and debugging

    -- | We can verify the correctness of the DSL code using the 'verifyDSL'
    -- function.

    -- | Use 'verifyDSLWith' to pass additional options to the solver.

    -- | Use 'verifyNumDSL' to verify rules that only involve numeric types (integer and real).
    -- To use this function, the rewrite should have the type @forall a. 'NumRule' a@, and the user can use the type parameter @a@ to specify the type of the tensor as:

    -- | @
    -- rule :: forall a. 'NumRule' a
    -- rule _ = do
    --   ...
    --   tensor <- newTensor \@a "tensor" ...
    -- @

    -- | Use 'verifyAnyDTypeDSL' to verify rules for all types (integer, real, boolean).
    -- To use this function, the rewrite should have the type @forall a. 'AnyDTypeRule' a@, and the user can use the type parameter @a@ to specify the type of the tensor as:

    -- | @
    -- rule :: forall a. 'AnyDTypeRule' a
    -- rule _ = do
    --   ...
    --   tensor <- newTensor \@a "tensor" ...
    -- @

    -- | See the [verification]("TensorRight#g:verify") section for more details.

    -- | On failure, these functions will print various information. To help understand the
    -- failure better, we also provide a set of monitoring functions, which can
    -- be used to print the shapes of expressions, or the contents of maps, etc.
    -- on failure.
    --
    -- The following code monitors whether the lhs tensor is valid, and if valid
    -- monitors its shape. It also monitors the content of the @low@ map on
    -- failure.

    -- | @
    -- 'monitorExprOnFailure' "lhs" lhs
    -- 'monitorMapOnFailure' "low" (ByRClass spatial) low
    -- @

    -- * Differences from the Paper

    --

    -- | The TensorRight paper introduces aggregated-axes as a set of named-axes
    -- and RClasses as a property of a family of aggregated-axes, such that:
    --
    -- - Each aggregated-axes has exactly one RClass.
    -- - All aggregated-axes having the same RClass always have the same rank.
    --
    -- Meanwhile, in our DSL implementation, we introduce RClasses as a set of
    -- named-axes, and we allow duplicate RClasses in a tensor's shape. We also
    -- allow the user to label duplicate RClasses to disambiguate them.
    -- These labels play the role of aggregated-axes in case of labelled
    -- RClasses. Meanwhile, in the case of unlabelled RClasses, the RClasses
    -- themselves play the role of aggregated-axes.
    -- This is only a syntactic difference, and the semantics of the DSL
    -- implementation are the same as the paper.

    -- * Rewriting rule context
    DSLContext,
    Rewrite (..),
    ValidElem,
    ValidNum,
    AnyDTypeRule,
    NumRule,
    rewrite,

    -- * Creation
    RClassRef (..),
    newRClass,
    newRClasses,
    newMap,
    newMaps,
    newNonNegMap,
    newNonNegMaps,
    newConstMap,
    newConstMaps,
    sumMap,
    combineMap,
    newTensor,
    DType (..),

    -- * Conditions #precond#

    -- | Apart from the helpers provided below, some Grisette operators are also
    -- useful, like 'Grisette..==', 'Grisette.symIte', etc.
    siRelation,
    checkSIMap,
    precondition,
    siRelation',
    precondition',
    numTensorAssumption,
    zipCondition,
    elemWiseCond,
    unaryCond,
    elemWiseArith,
    unaryArith,

    -- * Elements

    -- * Operations #op#
    ToElem (..),
    NumBinOp (..),
    numBinOp,
    numBinScalarOp,
    BoolBinOp (..),
    boolBinOp,
    boolBinScalarOp,
    CompareOp (..),
    compareOp,
    NumUnaryOp (..),
    numUnaryOp,
    BoolUnaryOp (..),
    boolUnaryOp,
    reduce,
    broadcast,
    constant,
    iota,
    Slice (..),
    slice,
    Padding (..),
    intElem,
    boolElem,
    pad,
    padLow,
    relabel,
    DySlice (..),
    dynamicSlice,
    dynamicUpdateSlice,
    concatTensor,
    concatTensorList,
    dot,
    ConvConfig (..),
    ConvPadding (..),
    convBase,
    conv,
    clamp,
    clampScalar,
    select,
    reverseTensor,
    reshapeDegenerate,

    -- * Monitoring
    monitorExprOnFailure,
    monitorMapOnFailure,

    -- * Verification #verify#
    verifyDSL,
    verifyDSLWith,
    verifyAnyDTypeDSL,
    verifyAnyDTypeDSLWith,
    verifyNumDSL,
    verifyNumDSLWith,

    -- * Syntax
    ArrowSyntax (..),
    AtSyntax (..),

    -- * Tensor int
    TensorNum,
    TensorReal,
    TensorInt,
    nonInf,
    posInf,
    negInf,

    -- * Utils
    printTitle,
  )
where

import TensorRight.Internal.Core.Tensor (ToElem (..))
import TensorRight.Internal.Core.Tensor.TensorInt
import TensorRight.Internal.DSL.Condition
import TensorRight.Internal.DSL.DSL
import TensorRight.Internal.DSL.Expr
import TensorRight.Internal.DSL.Syntax
import TensorRight.Internal.DSL.Verify
import TensorRight.Internal.Util.Pretty
