{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveGeneric #-}


-- FIXME need?
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Expresso.Syntax where

import qualified Data.Text as T
import Expresso.Type
import Expresso.Utils
import Data.Void

import Control.Applicative
import GHC.Generics(Generic, Generic1)
import qualified Data.Aeson as A

#if __GLASGOW_HASKELL__ <= 708
import Data.Foldable
import Data.Traversable
#endif

-- | Expression with imports unresolved.
type ExpI  = Fix ExpFI
-- | Expression with imports resolved at the top-level.
type ExpITopLevel = ExpF_ Name Bind Type I ExpI

-- | Expression with static expressions unresolved.
type ExpS  = Fix ExpFS
type ExpSI = Fix ExpFSI
type ExpSITopLevel = ExpF_ Name Bind Type I ExpSI

-- | Expression with imports and static expression resolved.
type Exp   = Fix ExpF

-- | Remote expression.
type ExpR  = ExpF_ Name Bind Type (K R) R

-- | Remote reference.
type R     = String

-- | An expression to  be evaluated at compile-time.
newtype Static = Static { unStatic :: Exp }
  deriving (Generic)

{- instance A.ToJSON Static -}
{- instance A.FromJSON Static -}

-- | Local include of another expression.
newtype Import = Import { unImport :: FilePath }
  deriving (Eq, Show, Generic)

instance A.ToJSON Import
instance A.FromJSON Import

-- TODO move
instance A.FromJSON Void where
  parseJSON _ = empty
instance A.ToJSON Void where
  toJSON = absurd
instance A.FromJSON Pos where
  parseJSON _ = pure dummyPos -- error "FIXME fromJSON Pos"
instance A.ToJSON Pos where
  toJSON _ = A.toJSON ("<pos>"::String) --error "FIXME fromJSON Pos"

type ExpF  = ExpF_ Name Bind Type I `Product` K Pos
type ExpFS  = (ExpF_ Name Bind Type I `Sum` K Static)`Product` K Pos
type ExpFI  = (ExpF_ Name Bind Type I `Sum` K Import) `Product` K Pos
type ExpFSI = ((ExpF_ Name Bind Type I `Sum` K Static) `Sum` K Import) `Product` K Pos

data ExpF_ v b t p r
  = EVar  v
  | EPrim (Prim_ p)
  | EApp  r r
  | ELam  (b v) r
  | EAnnLam (b v) t r
  | ELet  (b v) r r
  | ERef  R t
  | EAnn  r t
  deriving (Show, Functor, Foldable, Traversable, Generic, Generic1)

instance (A.ToJSON (b v), A.ToJSON v, A.ToJSON1 p, A.ToJSON (p Void), A.ToJSON t)
  => A.ToJSON1 (ExpF_ v b t p)
{- instance A.FromJSON1 (Ep -}

{- instance (A.ToJSON (b v), A.ToJSON v, A.ToJSON1 p, A.ToJSON (p Void), A.ToJSON t) => A.ToJSON1 (ExpF_ v b t p) -}
instance (A.ToJSON (b v), A.ToJSON v, A.ToJSON1 p, A.ToJSON (p Void), A.ToJSON t, A.ToJSON r) => A.ToJSON (ExpF_ v b t p r)
instance
  (A.FromJSON (b v)
  , A.FromJSON v
  , A.FromJSON1 p
  , A.FromJSON (p Void)
  , A.FromJSON t
  , A.FromJSON r
  )
    => A.FromJSON (ExpF_ v b t p r)
{- deriving instance A.FromJSON (ExpF_ -}

data Bind v
  = Arg v
  | RecArg [v]
  | RecWildcard
  deriving (Show, Generic)

instance A.FromJSON a => A.FromJSON (Bind a)
instance A.ToJSON a => A.ToJSON (Bind a)
{- instance A.FromJSON1 Bind -}

type Prim = Prim_ I
data Prim_ f
  = Int Integer
  | Dbl Double
  | Bool Bool
  | Char Char
  | Text T.Text
  | Blob (f Void) -- We disallow embedding blobs in the AST directly, use ERef/ExpR to embed blobs

  | Show
  | Trace
  | ErrorPrim
  | ArithPrim ArithOp
  | RelPrim   RelOp
  | Not
  | And
  | Or
  | Eq
  | NEq
  | Double      -- double from int
  | Floor
  | Ceiling
  | Abs
  | Neg
  | Mod
  | CharToInt
  | IntToChar
  | Cond
  | FixPrim
  | FwdComp
  | BwdComp

  | PackBlob
  | UnpackBlob
  | PackText
  | UnpackText

  {-  | JustPrim -}
  {-  | NothingPrim -}
  {-  | MaybePrim -}

  | ListEmpty
  | ListCons
  | ListNull    -- needed if list elems have no equality defined
  | ListAppend
  | ListFoldr

  | RecordEmpty -- a.k.a. Unit
  | RecordSelect Label
  | RecordExtend Label
  | RecordRestrict Label
  | Absurd
  | VariantInject Label
  | VariantEmbed Label
  | VariantElim Label
  deriving (Generic)


{- deriving instance Eq1 f => Eq (Prim_ f) -}
  {- (==) = eq1 -}
{- deriving instance Ord1 f => Ord (Prim_ f) -}
  {- compare = compare1 -}

-- FIXME move
{- instance A.FromJSON Void where -}
  {- parseJSON _ = empty -}

-- FIXME requires UndecidableInstances...
instance (A.ToJSON1 f, A.ToJSON (f Void)) => A.ToJSON (Prim_ f)
instance (A.FromJSON1 f, A.FromJSON (f Void)) => A.FromJSON (Prim_ f)

instance Show1 f => Show (Prim_ f) where
  showsPrec = error "FIXME"
  {- showsPrec = showsPrec1 -}

{- deriving (Eq, Ord, Show) -}

data ArithOp = Add | Mul | Sub | Div
  deriving (Eq, Ord, Show, Generic)

instance A.ToJSON ArithOp
instance A.FromJSON ArithOp

data RelOp   = RGT  | RGTE | RLT  | RLTE
  deriving (Eq, Ord, Show, Generic)

instance A.ToJSON RelOp
instance A.FromJSON RelOp
