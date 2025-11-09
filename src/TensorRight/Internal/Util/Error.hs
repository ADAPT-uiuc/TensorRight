{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TensorRight.Internal.Util.Error
  ( Error,
    ErrorEnv,
    assert,
    splitWithError,
    tshow,
  )
where

import Control.Monad.Error.Class (MonadError (throwError))
import Control.Monad.Except (ExceptT, runExceptT)
import Data.Either (isRight)
import qualified Data.Text as T
import Grisette
  ( Mergeable,
    PlainUnion (toGuardedList),
    SymBool,
    Union,
    mrgReturn,
  )
import Grisette.Unified (GetBool, UnifiedBranching, mrgIf)

type Error = T.Text

type ErrorEnv = ExceptT Error Union

assert ::
  (UnifiedBranching mode m, MonadError Error m) => Error -> GetBool mode -> m ()
assert err cond = mrgIf cond (return ()) $ throwError err

tshow :: Show a => a -> T.Text
tshow = T.pack . show

-- May introduce this into Grisette library in the future
splitWithError ::
  forall a. (Mergeable a) => ExceptT Error Union a -> Maybe (SymBool, Union a)
splitWithError a = do
  let joined :: Union (Either () (Union a)) = do
        v <- runExceptT a
        case v of
          Left _ -> mrgReturn $ Left ()
          Right v -> mrgReturn $ Right $ mrgReturn v
  let flattened = filter (\(_, v) -> isRight v) $ toGuardedList joined
  case flattened of
    [] -> Nothing
    [(b, Right v)] -> Just (b, v)
    _ -> error "Should not happen."
