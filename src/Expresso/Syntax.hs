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

module Expresso.Syntax where

import qualified Data.Text as T
import Expresso.Type
import Expresso.Utils
import Data.Void

#if __GLASGOW_HASKELL__ <= 708
import Data.Foldable
import Data.Traversable
#endif


-- | Expression with imports unresolved.
type ExpI  = Fix ((ExpF Name Bind Type I :+: K Import) :*: K Pos)
-- | Expression with imports resolved.
type Exp   = Fix ExpF'


type R     = String
-- | Remote expression.
type ExpR  = ExpF Name Bind Type (K R) R

newtype Import = Import { unImport :: FilePath }

type ExpF' = ExpF Name Bind Type I :*: K Pos
data ExpF v b t p r
  = EVar  v
  | EPrim (Prim_ p)
  | EApp  r r
  | ELam  (b v) r
  | EAnnLam (b v) t r
  | ELet  (b v) r r
  | ERef  R t
  | EAnn  r t
  deriving (Show, Functor, Foldable, Traversable)

data Bind v
  = Arg v
  | RecArg [v]
  | RecWildcard
  deriving Show

type Prim = Prim_ I
data Prim_ f
  = Int Integer
  | Dbl Double
  | Bool Bool
  | Char Char
  | String String
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
{- deriving instance Eq1 f => Eq (Prim_ f) -}
  {- (==) = eq1 -}
{- deriving instance Ord1 f => Ord (Prim_ f) -}
  {- compare = compare1 -}
instance Show1 f => Show (Prim_ f) where
  showsPrec = error "FIXME"
  {- showsPrec = showsPrec1 -}

{- deriving (Eq, Ord, Show) -}

data ArithOp = Add | Mul | Sub | Div
  deriving (Eq, Ord, Show)

data RelOp   = RGT  | RGTE | RLT  | RLTE
  deriving (Eq, Ord, Show)
