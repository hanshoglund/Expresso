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

module Expresso.Syntax where

import Expresso.Type
import Expresso.Utils

type ExpI  = Fix ((ExpF Name Bind :+: K Import) :*: K Pos)
type Exp   = Fix (ExpF Name Bind :*: K Pos)

newtype Import = Import { unImport :: FilePath }

data ExpF v b r
  = EVar  v
  | EPrim Prim
  | EApp  r r
  | ELam  (b v) r
  | ELet  (b v) r r
  deriving (Show, Functor, Foldable, Traversable)

data Bind v
  = Arg v
  | RecArg [v]
  | RecWildcard
  deriving Show

data Prim
  = Int Integer
  | Dbl Double
  | Bool Bool
  | Char Char
  | String String
  | Show
  | Trace
  | ErrorPrim
  | ArithPrim ArithOp
  | RelPrim   RelOp
  | Not
  | Eq
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
  | JustPrim
  | NothingPrim
  | MaybePrim
  | ListEmpty
  | ListCons
  | ListNull    -- needed if list elems have no equality defined
  | ListAppend
  | ListFoldr
  | RecordEmpty -- a.k.a. Unit
  | RecordSelect Label
  | RecordExtend Label
  | RecordRestrict Label
  | EmptyAlt
  | VariantInject Label
  | VariantEmbed Label
  | VariantElim Label
  deriving (Eq, Ord, Show)

data ArithOp = Add | Mul | Sub | Div
  deriving (Eq, Ord, Show)

data RelOp   = RGT  | RGTE | RLT  | RLTE
  deriving (Eq, Ord, Show)
