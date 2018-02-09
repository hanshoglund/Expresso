{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-dodgy-exports #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE CPP #-}
module Expresso.Utils
(
  module Data.Functor.Identity,
  module Data.Functor.Product,
  module Data.Functor.Sum,
  module Data.Functor.Classes,
#if __GLASGOW_HASKELL__ <= 708
  module Data.Functor.Constant,
#else
  module Data.Functor.Const,
  pattern Constant,
#endif
  Fix(..),
  K,
  pattern K,
  unK,
  I,
  pattern (:*:),
  (:+:)(..),
  (:*:)(..),
  left,
  right,
  cata,
  cataM,
  para,
  ana,
  (&&&),
  (***),
  first,
  second,
  showError,
  View(..),
  annotate,
  stripAnn,
  getAnn,
  withAnn
)
where

import Prelude hiding (mapM)
import Control.Monad hiding (mapM)
import Data.Foldable
import Data.Traversable
import Data.Functor.Identity
import Data.Functor.Classes
import Data.Functor.Product
import Data.Functor.Sum
import Data.Aeson -- (FromJSON, ToJSON, FromJSON1, ToJSON1)
import qualified Data.Aeson.Encoding as E
import qualified Data.HashMap.Strict as H
import qualified Data.Aeson as A
import qualified Data.Aeson.Types as A
import GHC.Generics (Generic, Generic1)
import Control.Applicative


#if __GLASGOW_HASKELL__ <= 708
import Data.Functor.Constant
# define CONST Constant
#else
import Data.Functor.Const
# define CONST Const
#endif

newtype Fix f = Fix { unFix :: f (Fix f) }

{-
 (
    (A.Value -> A.Parser (Fix f))
    -> (A.Value -> A.Parser [Fix f])
    -> A.Value
    -> A.Parser (f (Fix f)))

    -> A.Value

    -> A.Parser (Fix f)


 -
 - -}

instance A.FromJSON1 f => A.FromJSON (Fix f) where
  parseJSON v =
    let liftParse = (A.liftParseJSON :: (A.Value -> A.Parser (Fix f)) -> (A.Value -> A.Parser [Fix f]) -> A.Value -> A.Parser (f (Fix f)))
    in Fix <$> (liftParse A.parseJSON (error "f") v)
instance A.ToJSON1 f => A.ToJSON (Fix f) where
  toJSON (Fix f) =
    let liftToJSON = (A.liftToJSON :: (Fix f -> A.Value) -> ([Fix f] -> A.Value) -> f (Fix f) -> A.Value)
    in liftToJSON A.toJSON (error "g") f




#if __GLASGOW_HASKELL__ <= 708
type K = Constant

unK :: Constant a b -> a
unK = getConstant

pattern K a = Constant a
#else
type K = Const

unK :: Const a b -> a
unK = getConst

pattern K a = Const a
pattern Constant a = Const a
#endif



-- TODO move

#if __GLASGOW_HASKELL__ <= 708
deriving instance Generic1 (CONST a)
instance A.FromJSON a => A.FromJSON1 (CONST a) where
  liftParseJSON _ _ x = Constant <$> A.parseJSON x
instance A.ToJSON a => A.ToJSON1 (CONST a) where
  liftToJSON _ _ (Constant x) = A.toJSON x
instance A.FromJSON a => A.FromJSON (CONST a b) where
  parseJSON x = Constant <$> A.parseJSON x
instance A.ToJSON a => A.ToJSON (CONST a b) where
  toJSON (Constant x) = A.toJSON x
#endif


{- instance (Generic1 f, Generic1 g) => Generic1 (f :*: g) -}


{- instance (A.FromJSON1 f, A.FromJSON1 g) => A.FromJSON1 (f :*: g) where -}
  {- liftParseJSON = undefined -}
{- {- liftParseJSON parse parseList x = -} -}
    {- {- liftA2 (:*:) -} -}
    {- {- (A.liftParseJSON parse parseList x -} -}
    {- {- ) -} -}
    {- {- (A.liftParseJSON parse parseList x -} -}
    {- {- ) -} -}

{- -- -}
{- instance (ToJSON1 f, ToJSON1 g, ToJSON a) => ToJSON (Product f g a) where -}
    {- toJSON = toJSON1 -}
    {- {-# INLINE toJSON #-} -}

    {- toEncoding = toEncoding1 -}
    {- {-# INLINE toEncoding #-} -}

{- instance (ToJSON1 f, ToJSON1 g) => ToJSON1 (Sum f g) where -}
    {- liftToJSON tv tvl (InL x) = Object $ H.singleton "InL" (liftToJSON tv tvl x) -}
    {- liftToJSON tv tvl (InR y) = Object $ H.singleton "InR" (liftToJSON tv tvl y) -}

    {- liftToEncoding te tel (InL x) = E.pairs $ E.pair "InL" $ liftToEncoding te tel x -}
    {- liftToEncoding te tel (InR y) = E.pairs $ E.pair "InR" $ liftToEncoding te tel y -}
{- --- -}



type I = Identity

type (f :*: g) a = Product f g a

pattern f :*: g = Pair f g
left (Pair x y) = x
right (Pair x y) = y
{- data (f :*: g) a = (:*:) { left :: f a, right :: g a } -}
  {- deriving (Eq, Ord, Show, Functor, Foldable, Traversable) -}


type (f :+: g) a = Sum f g a
{- data (f :+: g) a = InL (f a) | InR (g a) -}
  {- deriving (Eq, Ord, Show, Functor, Foldable, Traversable) -}

cata :: Functor f => (f a -> a) -> Fix f -> a
cata phi = phi . fmap (cata phi) . unFix

cataM :: (Monad m, Traversable f) =>
         (f a -> m a) -> Fix f -> m a
cataM algM = algM <=< (mapM (cataM algM) . unFix)

para :: Functor f => (f (b, Fix f) -> b) -> Fix f -> b
para phi = phi . fmap (para phi &&& id) . unFix

ana :: Functor f => (a -> f a) -> a -> Fix f
ana coalg = Fix . fmap (ana coalg) . coalg

-- Equivalent to specialized version from Arrow
(&&&) :: (a -> b) -> (a -> c) -> (a -> (b,c))
f &&& g = \a -> (f a, g a)

-- Equivalent to specialized version from Arrow
(***) :: (a -> b) -> (c -> d) -> ((a, c) -> (b, d))
f *** g = \(a, b) -> (f a, g b)

-- Equivalent to specialized version from Arrow
first :: (a -> b) -> (a,c) -> (b,c)
first f (a,c) = (f a, c)

-- Equivalent to specialized version from Arrow
second :: (b -> c) -> (a,b) -> (a,c)
second f (a,b) = (a, f b)

instance (Functor f, Show (f (Fix f))) => Show (Fix f) where
    showsPrec d (Fix f) = showsPrec d f

instance (Functor f, Eq (f (Fix f))) => Eq (Fix f) where
    fa == fb = unFix fa == unFix fb

instance (Functor f, Ord (f (Fix f))) => Ord (Fix f) where
    compare fa fb = compare (unFix fa) (unFix fb)

class View f a where
  proj :: a -> f a
  inj  :: f a -> a

showError :: Show a => Either a b -> Either String b
showError = either (Left . show) Right

-- | add annotation
annotate :: forall f a. Functor f => a -> Fix f -> Fix (f `Product` K a)
annotate ann = cata alg where
  alg :: f (Fix (f `Product` K a)) -> Fix (f `Product` K a)
  alg e = Fix (e :*: K ann)

-- | strip annotations
stripAnn :: forall f a. Functor f => Fix (f `Product` K a) -> Fix f
stripAnn = cata alg where
  alg :: (f :*: K a) (Fix f) -> Fix f
  alg (e :*: _) = Fix e
  alg _ = error "safe: not detected due to GHC pattern synonym limitation"

-- | retrieve annotation
getAnn :: Fix (f `Product` K a) -> a
getAnn = unK . right . unFix

-- | fix with annotation
withAnn :: a -> f (Fix (f `Product` K a) )-> Fix (f `Product` K a)
withAnn ann e = Fix (e :*: K ann)
