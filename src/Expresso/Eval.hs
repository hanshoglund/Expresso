{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}


#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

------------------------------------------------------------
--
-- A lazy evaluator.
--
-- The front-end syntax is simple, so we evaluate it directly.
--
module Expresso.Eval(
    eval
  , bind
  , ppValue
  , ppValue'

  , Env
  , EvalM
  , EvalIO
  , runEvalM
  , runEvalIO
  , runEvIO'
  , ValueF(..)
  , ThunkF(..)
  , Value
  , Thunk
  , Env'
  , Value'
  , Thunk'
  , EnvIO
  , ValueIO
  , ThunkIO

{- , force -}

  , HasType(..)
  , FromValue(..)
  , fromValue1
  , fromValue2
  , ToValue(..)
  , MonadEval(..)

  -- TODO testing
  , V1(..)
  , V2(..)
  , V3(..)
  , V4(..)
  , roundTrip
)
where

import Data.Hashable
import Control.Monad.Except hiding (mapM)
import Control.Monad.State hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Applicative
import Control.Arrow (Kleisli(..))
import Data.Bifunctor (first)
import Data.Functor.Compose
import Data.Foldable (foldrM, toList)
import Data.Map (Map)
import Data.HashMap.Strict (HashMap)
import Data.Coerce
import Data.Maybe
import Data.Monoid
import Data.Ord
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HashMap
import qualified Data.List as List
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as T
import Control.Monad.ST
import Data.STRef
import Data.Void
import Data.Functor.Identity
import Data.Proxy
import qualified GHC.Generics as G
import GHC.TypeLits
import Control.Exception (IOException, catch)

import Expresso.Syntax
import Expresso.Type
import Expresso.Pretty
import Expresso.Utils (cata, (:*:)(..), K(..))
import qualified Expresso.Parser as Parser

{- import Control.Monad.Log hiding (Trace) -}
import Control.Monad.Var hiding (Var)
import qualified Control.Monad.Var as Var

#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (mapM, concat, elem, and, any)
import Data.Foldable
import Data.Traversable
#endif

type f ~> g = forall x . f x -> g x
type ApplicativeMonadError e f = (Applicative f, Alternative f, MonadError e f)

-- |
-- Call-by-need environment
-- A HashMap makes it easy to support record wildcards
type Env f = HashMap Name (Thunk f)

-- | Basic implementation of MonadEval, which evaluates lazily
-- (TODO may not perform full call-by-need) and ignores most effects.
{- newtype EvalM a = EvalM { runEvalT :: ExceptT String Identity a } -}
{- deriving instance Functor EvalM -}
{- deriving instance Applicative EvalM -}
{- deriving instance Monad EvalM -}
{- deriving instance MonadError String EvalM -}
{- instance Alternative EvalM where -}
  {- EvalM a <|> EvalM b = EvalM (a <|> b) -}
  {- empty = EvalM empty -}
{- instance MonadEval EvalM where -}
  {- force = force_ -}
  {- delay = return . Thunk -}
  {- evalRef _ = toValue <$> pure () -}
  {- trace msg = pure () -}
  {- failed = throwError -}

runEvalIO :: EvalIO a -> IO a
{- runEvalIO = either error pure . runEvalM -}
runEvalIO = runEvIO

-- FIXME try to recast EvalM as (Ev (State (Map Text (Value EvalM)))) or similar, replacing MonadVar with
-- class MonadMonoVar f where
--   type Var f :: *
--   type Val f :: *
--   newVar :: Val f -> Var f
--      etc.
-- instance MonadMonoVar (State (Map k v) where
--   type Var (State (Map k v)) = k
--   type Val (State (Map k v)) = v
--      etc.


newtype EvalM a = EvalM { runEvalM_ :: ExceptT String Identity a }
deriving instance Functor EvalM
deriving instance Applicative EvalM
deriving instance Monad EvalM
deriving instance MonadError String EvalM
instance Alternative EvalM where
  EvalM a <|> EvalM b = EvalM (a <|> b)
  empty = EvalM empty
instance MonadEval EvalM where
  force = force_
  delay = return . Thunk
  evalRef _ = toValue <$> pure ()
  trace msg = pure ()
  failed = throwError

runEvalM = runExcept . runEvalM_






class MonadTrace f where
  trace_ :: String -> f ()
instance MonadTrace IO where
  trace_ = putStrLn


-- | Run in terms of
--
--    MonadError String
--    MonadVar for laziness
--    MonadLog for trace
newtype Ev (f :: * -> *) a = Ev { runEv_ :: ExceptT String f a }
deriving instance MonadTrans Ev
deriving instance (Applicative f, Monad f) => Functor (Ev f)
deriving instance (Applicative f, Monad f) => Applicative (Ev f)
deriving instance (Applicative f, Monad f) => Monad (Ev f)
deriving instance (Applicative f, Monad f) => Alternative (Ev f)
  {- Ev a <|> Ev b = Ev (a <|> b) -}
  {- empty = Ev empty -}
{- deriving instance MonadError String f => MonadError String (Ev f) -}
instance (Alternative f, MonadTrace f, MonadVar f) => MonadEval (Ev f) where
  trace x = lift $ trace_ x
  failed x = Ev $ throwError x
  evalRef x = error "TODO no evalRef"
  delay k = do
    v <- lift $ newVar Nothing
    pure $ Thunk $ do
      cur <- lift $ readVar v
      case cur of
        Just x -> pure x
        Nothing -> do
          r <- k
          lift $ writeVar v $ Just r
          pure r
  force (Thunk k) = k

runEv :: (Applicative f, Monad f, MonadError String f) => Ev f a -> f a
runEv = either throwError pure <=< runExceptT . runEv_

runEvST :: (forall s . Ev (ST s) a) -> (Either String a)
runEvST x = runST $ runExceptT $ runEv_ x

runEvIO :: Ev IO a -> IO a
runEvIO = either error pure <=< runExceptT . runEv_

runEvIO' :: Ev IO a -> ExceptT String IO a
runEvIO' = runEv_

{- runEvIO = either error pure . runEv -}

{- runEv :: Ev a -> Either String a -}
{- runEv = runIdentity . runExceptT . runEvalT -}





type EvalIO = Ev IO

type ValueIO = Value EvalIO
type ThunkIO = Thunk EvalIO
type EnvIO   = Env   EvalIO

type Value' = Value EvalM
type Thunk' = Thunk EvalM
type Env'   = Env   EvalM

type Thunk = ThunkF ()
newtype ThunkF hof qq = Thunk { force_ :: qq (ValueF hof qq) }


hoistThunk :: Functor f => (f ~> g) -> ThunkF Void f -> ThunkF Void g
hoistThunk f (Thunk t) = Thunk (f . fmap (hoistValue f) $ t)

hoistValue :: Functor f => (f ~> g) -> FirstOrderValue f -> FirstOrderValue g
hoistValue f = go
  where
    go (VLamF _ x) = absurd x
    go (VInt x) = VInt x
    go (VDbl x) = VDbl x
    go (VChar x) = VChar x
    go (VBool x) = VBool x
    go (VList xs) = VList (go <$> xs)
    go (VRecord xs) = VRecord (goT <$> xs)
    go (VVariant l t) = VVariant l (goT t)

    goT = hoistThunk f


-- |
-- This class describes a monad with the effects required
-- to evaluate an expression. They can be viewed as an
-- overloadable interpretation of effects in the source
-- language.
--
-- Along with FromValue and ToValue these give you an
-- interpretation of Expresso functions as Haskell
-- functions.
--
class (Applicative f, Monad f, Alternative f) => MonadEval f where
  force    :: Thunk f -> f (Value f)
  delay    :: f (Value f) -> f (Thunk f)
  evalRef  :: String -> f (Value f)
  trace    :: String -> f () -- TODO should be: String -> f ()
  failed   :: String -> f a

valueToThunk :: Applicative qq => Value qq -> Thunk qq
valueToThunk = Thunk . pure

instance Show (Thunk qq) where
    show _ = "<Thunk>"

type FirstOrderValue = ValueF Void

type Value = ValueF ()
pattern VLam x = VLamF x ()

data ValueF hof qq
  = VLamF     !(ThunkF hof qq -> qq (ValueF hof qq)) hof
  | VInt     !Integer
  | VDbl     !Double
  | VBool    !Bool
  | VChar    !Char
  {- | VMaybe   !(Maybe Value) -}
  | VList    ![ValueF hof qq] -- lists are strict
  | VRecord  !(HashMap Label (ThunkF hof qq)) -- field order no defined
  | VVariant !Label !(ThunkF hof qq)


instance Show Value' where
  -- TODO this doesn't just work for EvalM, but for any f where we have
  --  f ~> Either String
  show = showR . runEvalM . ppValue'


-- | This does *not* evaluate deeply
ppValue :: Value qq -> Doc
ppValue VLamF{}     = "<Lambda>"
ppValue (VInt  i)   = integer i
ppValue (VDbl  d)   = double d
ppValue (VBool b)   = if b then "True" else "False"
ppValue (VChar c)   = text $ c : []
{- ppValue (VMaybe mx) = maybe "Nothing" (\v -> "Just" <+> ppParensValue v) mx -}
ppValue (VList xs)
    | Just str <- mapM extractChar xs = string $ show str
    | otherwise     = bracketsList $ map ppValue xs
ppValue (VRecord m) = bracesList $ map ppEntry $ HashMap.keys m
  where
    ppEntry l = text l <+> "=" <+> "<Thunk>"
ppValue (VVariant l _) = text l <+> "<Thunk>"

ppParensValue :: Value qq -> Doc
ppParensValue v =
    case v of
        {- VMaybe{}   -> parens $ ppValue v -}
        VVariant{} -> parens $ ppValue v
        _          -> ppValue v

-- | This evaluates deeply
ppValue' :: MonadEval qq => Value qq -> qq Doc
ppValue' (VRecord m) = (bracesList . map ppEntry . List.sortBy (comparing fst) . HashMap.toList)
                           <$> mapM (force >=> ppValue') m
  where
    ppEntry (l, v) = text l <+> text "=" <+> v
ppValue' (VVariant l t) = (text l <+>) <$> (force >=> ppParensValue') t
ppValue' v = return $ ppValue v

ppParensValue' :: MonadEval qq => Value qq -> qq Doc
ppParensValue' v =
    case v of
        {- VMaybe{}   -> parens <$> ppValue' v -}
        VVariant{} -> parens <$> ppValue' v
        _          -> ppValue' v

extractChar :: Value qq -> Maybe Char
extractChar (VChar c) = Just c
extractChar _ = Nothing




eval :: forall qq . MonadEval qq => Env qq -> Exp -> qq (Value qq)
eval env e = cata alg e env
  where
    alg :: (ExpF Name Bind Type :*: K Pos) (Env qq -> qq (Value qq))
        -> Env qq
        -> qq (Value qq)
    alg (EVar v :*: _)         env = lookupValue env v >>= force
    alg (EApp f x :*: K pos)   env = do
        f' <- f env
        x' <- delay (x env)
        evalApp pos f' x'
    alg (ELam b e1 :*: _  )    env = evalLam env b e1
    alg (EAnnLam b _ e1 :*: _) env = evalLam env b e1
    alg (ELet b e1 e2 :*: _)   env = do
        t    <- delay $ e1 env
        env' <- bind env b t
        e2 env'
    alg (ERef x _ :*: pos)     _   = evalRef x
    alg (EPrim p :*: K pos)    _   = pure $ evalPrim pos p
    alg (EAnn e _ :*: _)       env = e env

evalLam :: MonadEval qq => Env qq -> Bind Name -> (Env qq -> qq (Value qq)) -> qq (Value qq)
evalLam env b e = return $ VLam $ \x ->
    bind env b x >>= e

evalApp :: MonadEval qq => Pos -> Value qq -> Thunk qq -> qq (Value qq)
evalApp _   (VLam f)   t  = f t
evalApp pos fv         _  =
    failed $ show pos ++ " : Expected a function, but got: " ++
                 show (ppValue fv)

-- | Look up a primitive.
--
-- Note: return type is not in qq, but the value returned may still be a function with
-- effects in qq (e.g. a VLam).
evalPrim :: forall qq . MonadEval qq => Pos -> Prim -> Value qq
evalPrim pos p = case p of
    Trace     -> VLam $ \s -> do
        msg <- fromValue' s
        trace msg
        pure $ VRecord mempty
    ErrorPrim     -> VLam $ \s -> do
        msg <- fromValue' s
        failed $ "error (" ++ show pos ++ "):" ++ msg

    Int i         -> VInt i
    Dbl d         -> VDbl d
    Bool b        -> VBool b
    Char c        -> VChar c
    String s      -> VList (fmap VChar s)
    Show          -> mkStrictLam $ \v -> string . show <$> ppValue' v
      where
        string = VList . fmap VChar


    Abs -> mkStrictLam  $ numOp1 pos abs
    ArithPrim Add -> mkStrictLam2 $ numOp pos (+)
    ArithPrim Sub -> mkStrictLam2 $ numOp pos (-)
    ArithPrim Mul -> mkStrictLam2 $ numOp pos (*)
    ArithPrim Div -> mkStrictLam2 $ \v1 v2 ->
        case (v1, v2) of
            (VInt x, VInt y) -> return $ VInt $ x `div` y
            (VDbl x, VDbl y) -> return $ VDbl $ x / y
            _                -> failOnValues pos [v1, v2]

    RelPrim RGT   -> mkStrictLam2 $ \v1 v2 ->
        (VBool . (==GT)) <$> compareValues pos v1 v2

    RelPrim RGTE  -> mkStrictLam2 $ \v1 v2 ->
        (VBool . (`elem` [GT, EQ])) <$> compareValues pos v1 v2

    RelPrim RLT   -> mkStrictLam2 $ \v1 v2 ->
        (VBool . (==LT)) <$> compareValues pos v1 v2

    RelPrim RLTE  -> mkStrictLam2 $ \v1 v2 ->
        (VBool . (`elem` [LT, EQ])) <$> compareValues pos v1 v2

    Eq            -> mkStrictLam2 $ \v1 v2 ->
        VBool <$> equalValues pos v1 v2

    NEq           -> mkStrictLam2 $ \v1 v2 ->
        (VBool . not) <$> equalValues pos v1 v2

    Not           -> VLam $ \v -> VBool <$> fromValue' v
    And           -> VLam $ \v1 -> return $ VLam $ \v2 ->
        VBool <$> ((&&) <$> fromValue' v1 <*> fromValue' v2)

    Or            -> VLam $ \v1 -> return $ VLam $ \v2 ->
        VBool <$> ((||) <$> fromValue' v1 <*> fromValue' v2)

    Double        -> mkStrictLam $ \v ->
        case v of
            VInt i -> return $ VDbl $ fromInteger i
            _      -> failOnValues pos [v]
    Floor         -> mkStrictLam $ \v ->
        case v of
            VDbl d -> return $ VInt $ floor d
            _      -> failOnValues pos [v]
    Ceiling       -> mkStrictLam $ \v ->
        case v of
            VDbl d -> return $ VInt $ ceiling d
            _      -> failOnValues pos [v]

    Neg           -> mkStrictLam $ \v ->
        case v of
            VInt i -> return $ VInt $ negate i
            VDbl d -> return $ VDbl $ negate d
            _      -> failOnValues pos [v]

    Mod           -> mkStrictLam $ \v1 -> return $ mkStrictLam $ \v2 ->
        case (v1, v2) of
            (VInt x, VInt y) -> return $ VInt $ x `mod` y
            _                -> failOnValues pos [v1, v2]

    Cond     -> VLam $ \c -> return $ VLam $ \t -> return $ VLam $ \f ->
        fromValue' c >>= \c -> if c then force t else force f
    FixPrim       -> mkStrictLam $ \f -> fix (evalApp pos f <=< delay)

    -- We cannot yet define operators like this in the language
    FwdComp       -> mkStrictLam2 $ \f g ->
        return $ VLam $ \x ->
            delay (evalApp pos f x) >>= evalApp pos g
    BwdComp    -> mkStrictLam2 $ \f g ->
        return $ VLam $ \x ->
            delay (evalApp pos g x) >>= evalApp pos f

    {- JustPrim      -> mkStrictLam $ \v -> return $ VMaybe (Just v) -}
    {- NothingPrim   -> VMaybe Nothing -}
    {- MaybePrim     -> VLam $ \x -> return $ mkStrictLam2 $ \f v -> -}
        {- case v of -}
            {- VMaybe (Just v') -> evalApp pos f (Thunk $ return v') -}
            {- VMaybe Nothing   -> force x -}
            {- _                -> failOnValues pos [v] -}

    ListEmpty     -> VList []
    ListNull      -> VLam $ \xs ->
        (VBool . (null :: [Value qq] -> Bool)) <$> (force >=> fromValueL return) xs
    ListCons      -> VLam $ \x -> return $ VLam $ \xs ->
        VList <$> ((:) <$> force x <*> (force >=> fromValueL return) xs)
    ListAppend    -> VLam $ \xs -> return $ VLam $ \ys ->
        VList <$> ((++) <$> (force >=> fromValueL return) xs <*> (force >=> fromValueL return) ys)
    ListFoldr     -> mkStrictLam $ \f ->
        return $ VLam $ \z -> return $ VLam $ \xs -> do
        let g a b = do g' <- evalApp pos f (Thunk $ return a)
                       evalApp pos g' (Thunk $ return b)
        z'  <- force z
        xs' <- (force >=> fromValueL return) xs -- :: qq [Value qq]
        foldrM g z' xs'
    RecordExtend l   -> VLam $ \v -> return $ VLam $ \r ->
        (VRecord . HashMap.insert l v) <$> (force >=> fromValueRTh) r
    RecordRestrict l -> VLam $ \r ->
        (VRecord . HashMap.delete l) <$> (force >=> fromValueRTh) r
    RecordSelect l   -> VLam $ \r -> do
        r' <- (force >=> fromValueRTh) r
        let err = failed $ show pos ++ " : " ++ l ++ " not found"
        maybe err force (HashMap.lookup l r')
    RecordEmpty -> VRecord mempty
    VariantInject l  -> VLam $ \v ->
        return $ VVariant l v
    VariantEmbed _   -> VLam force
    VariantElim l    -> mkStrictLam $ \f -> return $ mkStrictLam2 $ \k s -> do
        case s of
            VVariant l' t | l==l'     -> evalApp pos f t
                          | otherwise -> evalApp pos k (Thunk $ return s)
            v -> failed $ show pos ++ " : Expected a variant, but got: " ++
                              show (ppValue v)
    Absurd -> VLam $ \v -> force v >> failed "The impossible happened!"
    {- p -> error $ show pos ++ " : Unsupported Prim: " ++ show p -}


-- non-strict bind
bind :: MonadEval qq => Env qq -> Bind Name -> Thunk qq -> qq (Env qq)
bind env b t = case b of
    Arg n -> return $ HashMap.insert n t env
    _     -> bind' env b t

-- strict bind
bind' :: MonadEval f => Env f -> Bind Name -> Thunk f -> f (Env f)
bind' env b t = do
  v <- force t
  case (b, v) of
    (Arg n, _)               ->
        return $ HashMap.insert n (Thunk $ return v) env
    (RecArg ns, VRecord m) | Just vs <- mapM (\n -> HashMap.lookup n m) ns ->
        return $ env <> (HashMap.fromList $ zip ns vs)
    (RecWildcard, VRecord m) ->
        return $ env <> m
    _ -> failed $ "Cannot bind the pair: " ++ show b ++ " = " ++ show (ppValue v)

lookupValue :: MonadEval f => Env f -> Name -> f (Thunk f)
lookupValue env n = maybe err return $ HashMap.lookup n env
  where
    err = failed $ "Not found: " ++ show n

failOnValues :: MonadEval f => Pos -> [Value qq] -> f a
failOnValues pos vs = failed $ show pos ++ " : Unexpected value(s) : " ++
                                   show (parensList (map ppValue vs))

mkStrictLam :: MonadEval f => (Value f -> f (Value f)) -> Value f
mkStrictLam f = VLam $ \x -> force x >>= f

mkStrictLam2 :: MonadEval f => (Value f -> Value f -> f (Value f)) -> Value f
mkStrictLam2 f = mkStrictLam $ \v -> return $ mkStrictLam $ f v

fromValue' :: (MonadEval f, FromValue a) => Thunk f -> f a
fromValue' = force >=> fromValue

numOp :: MonadEval f => Pos -> (forall a. Num a => a -> a -> a) -> Value f -> Value f -> f (Value f)
numOp _ op (VInt x) (VInt y) = return $ VInt $ x `op` y
numOp _ op (VDbl x) (VDbl y) = return $ VDbl $ x `op` y
numOp p _  v1       v2       = failOnValues p [v1, v2]

numOp1 :: MonadEval f => Pos -> (forall a. Num a => a -> a) -> Value f -> f (Value f)
numOp1 _ op (VInt x) = return $ VInt $ op x
numOp1 p _  v1       = failOnValues p [v1]

-- NB: evaluates deeply
equalValues :: MonadEval f => Pos -> Value f -> Value f -> f Bool
equalValues _ (VInt i1)    (VInt i2)    = return $ i1 == i2
equalValues _ (VDbl d1)    (VDbl d2)    = return $ d1 == d2
equalValues _ (VBool b1)   (VBool b2)   = return $ b1 == b2
equalValues _ (VChar c1)   (VChar c2)   = return $ c1 == c2
equalValues p (VList xs)   (VList ys)
    | length xs == length ys = and <$> zipWithM (equalValues p) xs ys
    | otherwise = return False
{- equalValues p (VMaybe m1)  (VMaybe m2)  = -}
    {- case (m1, m2) of -}
      {- (Just v1, Just v2) -> equalValues p v1 v2 -}
      {- (Nothing, Nothing) -> return True -}
      {- _                  -> return False -}
equalValues p (VRecord m1) (VRecord m2) = do
    (ls1, vs1) <- unzip . recordValues <$> mapM force m1
    (ls2, vs2) <- unzip . recordValues <$> mapM force m2
    if length ls1 == length ls2 && length vs1 == length vs2
       then and <$> zipWithM (equalValues p) vs1 vs2
       else return False
equalValues p (VVariant l1 v1) (VVariant l2 v2)
    | l1 == l2  = join $ equalValues p <$> force v1 <*> force v2
    | otherwise = return False
equalValues p v1 v2 = failOnValues p [v1, v2]

-- NB: evaluates deeply
compareValues :: MonadEval f => Pos -> Value f -> Value f -> f Ordering
compareValues _ (VInt i1)    (VInt i2)    = return $ compare i1 i2
compareValues _ (VDbl d1)    (VDbl d2)    = return $ compare d1 d2
compareValues _ (VBool b1)   (VBool b2)   = return $ compare b1 b2
compareValues _ (VChar c1)   (VChar c2)   = return $ compare c1 c2
compareValues p (VList xs)   (VList ys)   = go xs ys
  where
    {- go :: [Value] -> [Value] -> f Ordering -}
    go []      []      = return EQ
    go (_:_)   []      = return GT
    go []      (_:_)   = return LT
    go (x:xs') (y:ys') = do
          c <- compareValues p x y
          if c == EQ
              then go xs' ys'
              else return c
{- compareValues p (VMaybe m1)  (VMaybe m2)  = -}
    {- case (m1, m2) of -}
      {- (Just v1, Just v2) -> compareValues p v1 v2 -}
      {- (Nothing, Nothing) -> return EQ -}
      {- (Nothing, Just{} ) -> return LT -}
      {- (Just{} , Nothing) -> return GT -}
compareValues p v1 v2 = failOnValues p [v1, v2]

-- | Used for equality of records, sorts values by key
recordValues :: HashMap Label a -> [(Label, a)]
recordValues = List.sortBy (comparing fst) . HashMap.toList




-- |
-- How to marshall Haskell contructors and selectors into Expresso types.
--
-- Included to make it easier to add options later...
data Options = Options

defaultOptions :: Options
defaultOptions = Options


-- | Haskell types with a corresponding Expresso type.
-- TODO generalize proxy?
class HasType a where
    typeOf :: HasType a => Proxy a -> Type
    default typeOf :: (G.Generic a, GHasType (G.Rep a)) => Proxy a -> Type
    typeOf = either id (renderADT . improveADT) . gtypeOf defaultOptions . fmap G.from

-- | Haskell types whose values can be converted to Expresso values.
--
-- We expect
--
-- @
-- typeOf (pure a) = typeOfValue (toValue a)
-- @
--
-- If a type is an instance of both 'FromValue' and 'ToValue', we expect:
-- @
-- fromValue . toValue = pure
-- @
class HasType a => ToValue a where
    toValue :: ToValue a => a -> Value'
    default toValue :: (G.Generic a, GToValue (G.Rep a)) => a -> Value'
    toValue = renderADTValue . improveADT . gtoValue defaultOptions . G.from

-- | Haskell types whose values can be represented by Expresso values.
class HasType a => FromValue a where
    fromValue :: MonadEval f => Value f -> f a
    default fromValue :: (G.Generic a, ADFor (G.Rep a) ~ Var, GFromValue (G.Rep a), MonadEval f) => Value f -> f a
    fromValue = runParser . fmap G.to . renderADParser . fixADNames $ gfromValue defaultOptions Proxy

class GHasType f where
    gtypeOf :: Options -> Proxy (f x) -> Either Type (ADT Type)
class GHasType f => GToValue f where
    gtoValue :: Options -> f x -> ADT Value'
class GHasType f => GFromValue f where
    type ADFor f :: C
    gfromValue :: MonadEval g => Options -> Proxy (f x) -> AD (ADFor f) (Parser g g) (f x)

-- | This thing is passed around when traversing generic representations of Haskell types to keep track
-- of the surrounding context. We need this to properly decompose Haskell ADTs with >2 constructors into
-- proper (right-associative) rows. For records we also keep track of the number of elements, so we
-- can generate default selector functions _1, _2, _3 etc.
{- data Ctx = NoCtx | Var | Rec Int -}
  {- deriving (Show) -}

{- setTag :: b -> (Maybe b, a) -> (Maybe b, a) -}
{- setTag b (_, a) = (Just b, a) -}

-- TODO this is not super-typed...

type ConstructorName = Name
type SelectorName = Name

-- | An algebraic data type.
data ADT a = ADT { getADT :: Map ConstructorName (Map SelectorName a) }
  deriving (Eq, Show, Functor)

-- | Replace all auto-generated names in products.
-- E.g. rewrites
--
--  {___a:A, ___b:B} -> {_1:A, _2:B}
fixConsNames :: ADT a -> ADT a
fixConsNames (ADT outer) = ADT (g <$> outer)
  where
    g inner
      | hasAutoKeys inner = replaceKeys (fmap (("_" <>) . show) [1..]) inner
      | otherwise = inner


    replaceKeys :: (Ord k, Hashable k) => [k] -> Map k a -> Map k a
    replaceKeys ks m = Map.fromList $ zip ks $ fmap snd $ Map.toList m

    -- TODO ugly hack, see below
    hasAutoKeys x = case List.find ("___" `List.isInfixOf`) $ Map.keys x of
      Nothing -> False
      _ -> True


improveADT :: ADT a -> ADT a
improveADT = fixConsNames

{-

  NOTE encoding variations:
    Note that the following types are isomorphic, but have different types and representations
    in Expresso:
      A
      {foo:A}
      <Foo:A>
    More notably, these unify:
      {bar:A,...} ~ {bar:A}
    while these do not:
      {bar:A,...} ~ A

    This gives us some ambiguity when encoding HS types.

    Removing singleton variants gives more natural encoding for normal tuples
      () ~ {}                 instead of  <() : {}>
      (a,b) ~ {_1:a, _2:b}    instead of  <(,) : {_1:a, _2:b}>
    but has the drawback of 'collapsing' newtypes:
      Sum Int ~ Int           insted of <Sum : Int>

    Disallowing singleton products is probably uncontroversial.
 -}


data C = Var | Rec | None
class NotVar c
instance NotVar None
instance NotVar Rec

-- Haskell style ADT
--
-- This could be relaxed to normal row-polymorphism by relaxing the constraint on selectors
data AD :: C -> (* -> *) -> * -> * where
  Singleton :: f a -> AD None f a
  -- Constructor/Selector 'resets' the prod/coprod context
  Constructor :: NotVar x   => String -> AD x f a -> AD Var f a
  Selector    :: (x ~ None) => String -> AD x f a -> AD Rec f a -- A Prod can only contain other Prods, Selector, or Terminal
  -- This implies every field has to be named
  Prod :: (a -> b -> c) -> AD Rec f a -> AD Rec f b -> AD Rec f c
  Terminal :: f a -> AD Rec f a

  -- A coprod can only contain other Coprods, Constructor, or Initial
  -- This implies every alternative has to be named
  Coprod :: (a -> c) -> (b -> c) -> AD Var f a -> AD Var f b -> AD Var f c
  Initial :: AD Var f a

data AD' where
  Singleton' :: AD'
  Constructor' :: String -> AD' -> AD'
  Selector' :: String -> AD' -> AD'
  Prod' :: AD' -> AD' -> AD'
  Coprod' :: AD' -> AD' -> AD'
  Initial' :: AD'
  Terminal' :: AD'
  deriving (Show)

instance Show (AD x f a) where
  show = show . go
    where
      go :: forall x f a . AD x f a -> AD'
      go (Singleton _) = Singleton'
      go (Constructor n a) = Constructor' n $ go a
      go (Selector n a) = Selector' n $ go a
      go (Prod _ a b) = Prod' (go a) (go b)
      go (Coprod _ _ a b) = Coprod' (go a) (go b)
      go Initial = Initial'
      go Terminal{} = Terminal'

instance Functor f => Functor (AD x f) where
  fmap f (Singleton fa) = Singleton $ fmap f fa
  fmap f (Constructor n x) = Constructor n (fmap f x)
  fmap f (Selector n x) = Selector n (fmap f x)
  fmap f (Terminal fa) = Terminal $ fmap f fa
  fmap f Initial = Initial
  fmap f (Prod g a b) = Prod (\a b -> f $ g a b) a b
  fmap f (Coprod g h a b) = Coprod (f . g) (f . h) a b


renderADT :: ADT Type -> Type
renderADT (ADT outer)
  = foldOrSingle
    _TVariant (\k v -> _TRowExtend k (g v)) _TRowEmpty
    -- Remove singleton variants
    (\k m -> g m)
    -- Allowing them would look like this (e.g. a normal foldrWithKey)
    {- (\k v -> _TVariant $ _TRowExtend k (g v) _TRowEmpty) -}
    outer
  where
    g inner
      = foldOrSingle
        _TRecord (\k v -> _TRowExtend k v) _TRowEmpty
          -- A fold for general products/records
        (flip const)
        -- Remove singleton products
        {- (\k v -> _TRecord $ _TRowExtend k v _TRowEmpty) -}
        inner


renderADTValue :: Applicative qq => ADT (Value qq) -> Value qq
renderADTValue (ADT outer)
  = foldOrSingle
    -- TODO clean up this error printing...
    id (\k v r -> error $ "unexpected variant with >1 element"
          -- <> show (k,runEvalM.ppValue' $ g v,runEvalM.ppValue' $ r)
          ) (error "absurd!")
    (\k v -> VVariant k $ valueToThunk $ g v)
    outer
  where
    g inner
      = foldOrSingle
        VRecord (\k v -> HashMap.insert k (valueToThunk v)) mempty
        (\_ v -> v)
        inner

-- Would be a nice implementation, but the (Alternative Compose ...) instance is too restrictive
--
-- DerivingVia anyone?
--
--     type Parser f = ((->) Value) `Compose` f
--     _Parser = Compose
--     runParser = getCompose

-- FIXME when composed with EvalM, this concatenates error messages...
type Parser qq f = ReaderT (Value qq) f
_Parser = ReaderT
runParser = runReaderT



intoRecord :: (Applicative f, MonadState RecNames f) => f ()
intoRecord = put $ RecNames 1

nextName :: (Applicative f, MonadState RecNames f) => f (Maybe String)
nextName = do
  st <- get
  case st of
    RecNamesInit -> pure Nothing
    RecNames n -> do
      put $ RecNames $ n + 1
      pure $ Just $ "_" <> show n

{- chooseP :: Alternative f => Parser f a -> Parser f a -> Parser f a -}
{- chooseP = (<|>) -}

-- FIXME
{- traceP x = trace (show x) x -}


data RecNames
  = RecNamesInit -- We are not in a product
  | RecNames Int -- We are in a product, and this is the next name to generate

-- | Remove singleton selectors.
-- Rename anonymous '' selectors with _1, _2 etc.
fixADNames :: AD Var f a -> AD Var f a
fixADNames x = evalState (go x) RecNamesInit
  where
    go :: AD Var f a -> State RecNames (AD Var f a)
    go x@Initial{} = pure x
    go (Coprod f g x y) = Coprod f g <$> go' x <*> go' y
    go (Constructor k a) = Constructor k <$> go' a

    go' :: AD x f a -> State RecNames (AD x f a)
    go' x@Singleton{} = pure x
    go' x@Terminal{} = pure x
    go' (Prod f x y) = do
      intoRecord
      Prod f <$> go' x <*> go' y
    go' (Selector k a) = do
      name <- nextName
      case name of
        Nothing -> Selector "" <$> go' a
        Just n  -> Selector n <$> go' a
    go' x@Initial{} = go x
    go' x@Coprod{} = go x
    go' x@Constructor{} = go x

renderADParser :: MonadEval f => AD Var (Parser f f) a -> Parser f f a
renderADParser x = evalState (go x) 0
  where
    go :: forall f a . MonadEval f => AD Var (Parser f f) a -> State Int (Parser f f a)
    go Initial = pure empty
    go (Coprod f g x y) = liftA2 (<|>) (fmap f <$> go x) (fmap g <$> go y)
    go (Constructor k a) = do
      p <- go' a
      pure $ _Parser $ \x -> case x of
        (VVariant n th) | n == k -> do
          y <- force th
          runParser p y
        _ -> failed $ "Bad variant, wanted " <> k <> " got (" <> show (ppValue x) <> ")"

    go' :: forall f x a . MonadEval f => AD x (Parser f f) a -> State Int (Parser f f a)
    go' (Singleton p) = pure p
    go' (Terminal x) = pure x
    go' (Prod f x y) = do
      a' <- go' x
      b' <- go' y
      pure $ liftA2 f a' b'
    go' (Selector k x) = do
      p <- go' x
      case k of
        "" -> pure p
        _ ->
          pure $ _Parser $ \x -> case x of
            (VRecord m) -> case HashMap.lookup k m of
              Just th -> do
                v <- force th
                runParser p v
              _ -> fail k m
            _ -> failed $ "Not a record" -- FIXME, wanted '"<> k <>"', got (" <> (showR $ runEvalM $ ppValue' x) <> ")"
      where
        fail k m = failed $ "Bad record" -- FIXME , wanted '" <> k <> "', got rec with keys " <> show (HashMap.keys m)

    go' x@Initial{} = go x
    go' x@Coprod{} = go x
    go' x@Constructor{} = go x


-- TODO move
foldOrSingle :: (b -> c) -> (k -> a -> b -> b) -> b -> (k -> a -> c) -> Map k a -> c
foldOrSingle post f z o x = case Map.toList x of
  [(k, v)] -> o k v
  _ -> post $ Map.foldrWithKey f z x

singleton :: a -> ADT a
singleton v = ADT $ Map.singleton "" $ Map.singleton "" v

selector :: SelectorName -> ADT a -> ADT a
selector k (ADT outer) = ADT (g <$> outer)
  where
    g inner
      | Map.size inner == 1 = Map.singleton k (head $ toList inner)
      | otherwise = error "ADT: Unexpected"

constructor :: SelectorName -> ADT a -> ADT a
constructor k (ADT outer) = ADT $ g outer
  where
    g x
      | Map.size x == 1 = Map.singleton k (head $ toList x)
      | otherwise = error "ADT: Unexpected"


prod :: ADT a -> ADT a -> ADT a
prod (ADT l) (ADT r)
  | hasAmbNamesF l || hasAmbNamesF r = ADT $ Map.unionWith unionDisamb l r
  | otherwise                        = ADT $ Map.unionWith Map.union l r
  where
    hasAmbNamesF = any hasAmbNames
    hasAmbNames :: Map Name a -> Bool
    hasAmbNames = not . null . filter (== "") . Map.keys

    -- Haskell allows positional products (aka "tuples"), so we need to
    -- make up names to avoid ambiguity.
    --
    -- As we don't know how products will be nested, we just make up something
    -- preserving order. At the top level we will overwrite this with: _1, _2,
    -- etc.
    --
    -- TODO this is a hack, replace the special strings with (Either [Int] String)
    -- or something.
    unionDisamb :: Map Name a -> Map Name a -> Map Name a
    unionDisamb a b = mapKeys ("___a"<>) a `Map.union` mapKeys ("___b"<>) b

    mapKeys f = Map.fromList . fmap (first f) . Map.toList

coprod :: ADT a -> ADT a -> ADT a
coprod (ADT l) (ADT r) = ADT (l `Map.union` r)

inL :: ADT a -> ADT a
inR :: ADT a -> ADT a
inL = id
inR = id


initial :: ADT a
initial = ADT mempty

terminal :: ADT a
terminal = ADT (Map.singleton "()" $ mempty)


-- G.1 is based on embedding Hask in the functor category [Hask,Hask]
-- These synonyms make it a bit more clear what's going on
pattern Id a = G.M1 a
runId        = G.unM1
runConst     = G.unK1

-- TODO remove Either in return type of gtypeOf if Left is not used...
-- TODO move
instance (GHasType f, G.Constructor c) => GHasType (G.C1 c f) where
  gtypeOf opts x = fmap (constructor $ G.conName m) $ gtypeOf opts (runId <$> x)
    where m = (undefined :: t c f a)
instance (GHasType f, G.Selector c) => GHasType (G.S1 c f) where
  gtypeOf opts x = fmap (selector $ G.selName m) $ gtypeOf opts (runId <$> x)
    where m = (undefined :: t c f a)
instance GHasType f => GHasType (G.D1 c f) where
  gtypeOf opts x = gtypeOf opts (runId <$> x)

instance GHasType (G.U1) where
  gtypeOf _ _ = pure $ terminal
instance GHasType (G.V1) where
  gtypeOf _ _ = pure $ initial
instance HasType c => GHasType (G.K1 t c) where
  -- FIXME recurse with opts
  -- hows does aeson achieve it (without polluting the top-level class?)
  gtypeOf opts p = pure $ singleton $ typeOf (runConst <$> p)
instance (GHasType f, GHasType g) => GHasType (f G.:+: g) where
  gtypeOf opts p = coprod <$> (gtypeOf opts lp) <*> (gtypeOf opts rp)
    where
      lp = leftP p
      rp = rightP p
instance (GHasType f, GHasType g) => GHasType (f G.:*: g) where
  gtypeOf opts p = prod <$> (gtypeOf opts lp) <*> (gtypeOf opts rp)
    where
      lp = leftP p
      rp = rightP p



leftP :: forall (q :: (k -> k) -> (k -> k) -> k -> k) f g a . Proxy ((f `q` g) a) -> Proxy (f a)
leftP _ = Proxy

rightP :: forall (q :: (k -> k) -> (k -> k) -> k -> k) f g a . Proxy ((f `q` g) a) -> Proxy (g a)
rightP _ = Proxy



instance (GToValue f, G.Constructor c) => GToValue (G.C1 c f) where
  gtoValue opts x = (constructor $ G.conName m) $ gtoValue opts (runId x)
    where m = (undefined :: t c f a)

instance (GToValue f, G.Selector c) => GToValue (G.S1 c f) where
  gtoValue opts x = (selector $ G.selName m) $ gtoValue opts (runId x)
    where m = (undefined :: t c f a)

instance GToValue f => GToValue (G.D1 c f) where
  gtoValue opts x = gtoValue opts (runId x)

instance ToValue c => GToValue (G.K1 t c) where
  gtoValue opts p = singleton $ toValue (runConst $ p)

instance GToValue G.U1 where
  gtoValue _ _ = terminal

instance GToValue G.V1 where
  gtoValue _ _ = initial

instance (GToValue f, GToValue g) => GToValue (f G.:+: g) where
  gtoValue opts (G.L1 x) = inL (gtoValue opts x)
  gtoValue opts (G.R1 x) = inR (gtoValue opts x)

-- TODO get tag from underlying value...
instance (GToValue f, GToValue g) => GToValue (f G.:*: g) where
  gtoValue opts (lp G.:*: rp) = prod (gtoValue opts lp) (gtoValue opts rp)


_Id :: f x -> G.M1 t c f x
_Id = G.M1

_Const :: c -> G.K1 i c x
_Const = G.K1


instance (GFromValue f, NotVar (ADFor f), G.Constructor c) => GFromValue (G.C1 c f) where
  type ADFor (G.C1 c f) = Var
  gfromValue opts p = fmap _Id $ Constructor (G.conName m) $ gfromValue opts (runId <$> p)
    where m = (undefined :: t c f a)
instance (GFromValue f, ADFor f ~ None, G.Selector c) => GFromValue (G.S1 c f) where
  type ADFor (G.S1 c f) = Rec
  gfromValue opts p = fmap _Id $ Selector (G.selName m) $ gfromValue opts (runId <$> p)
    where m = (undefined :: t c f a)
instance GFromValue f => GFromValue (G.D1 c f) where
  type ADFor (G.D1 c f) = ADFor f
  gfromValue opts p = fmap _Id $ gfromValue opts (runId <$> p)
instance FromValue c => GFromValue (G.K1 t c) where
  type ADFor (G.K1 t c) = None
  gfromValue opts p = Singleton $ fmap _Const $ _Parser fromValue
instance GFromValue G.U1 where
  type ADFor G.U1 = Rec
  gfromValue opts p = Terminal (pure $ G.U1)
instance GFromValue G.V1 where
  type ADFor G.V1 = Var
  gfromValue opts p = Initial
instance (GFromValue f, GFromValue g, ADFor f ~ Var, ADFor g ~ Var) => GFromValue (f G.:+: g) where
  type ADFor (f G.:+: g) = Var
  gfromValue opts p = Coprod (G.L1) (G.R1) (gfromValue opts lp) (gfromValue opts rp)
    where
      lp = leftP p
      rp = rightP p
instance (GFromValue f, GFromValue g, ADFor f ~ Rec, ADFor g ~ Rec) => GFromValue (f G.:*: g) where
  type ADFor (f G.:*: g) = Rec
  gfromValue opts p = Prod (G.:*:) (gfromValue opts lp) (gfromValue opts rp)
    where
      lp = leftP p
      rp = rightP p






inside :: proxy (f a) -> Proxy a
inside = const Proxy

dom :: proxy (a -> b) -> Proxy a
dom = const Proxy

codom :: proxy (a -> b) -> Proxy b
codom = inside


instance HasType Integer where
    typeOf _ = _TInt

instance ToValue Integer where
    toValue = VInt

instance FromValue Integer where
    fromValue (VInt i) = return i
    fromValue v        = failfromValue "VInt" v

instance HasType Int where
    typeOf _ = _TInt

instance ToValue Int where
    toValue = VInt . fromIntegral

instance FromValue Int where
    fromValue x = fromInteger <$> fromValue x

instance HasType Double where
    typeOf _ = _TDbl

instance ToValue Double where
    toValue = VDbl

instance FromValue Double where
    fromValue (VDbl d) = return d
    fromValue v        = failfromValue "VDbl" v

instance HasType Bool where
  typeOf _ = _TBool
instance ToValue Bool where
    toValue = VBool
instance FromValue Bool where
    fromValue (VBool b) = return b
    fromValue v         = failfromValue "VBool" v

instance ToValue Char where
    toValue = VChar
instance FromValue Char where
    fromValue (VChar c) = return c
    fromValue v         = failfromValue "VChar" v
instance HasType Char where
    typeOf _ = _TChar




instance (HasType a, HasType b) => HasType (a -> f b) where
    typeOf p = _TFun (typeOf $ dom p) (typeOf $ inside $ inside p)

class MonadEval (Arr f) => FromValue1 (f :: * -> * -> *) where
  type Arr f :: * -> *
  fv :: (FromValue b, ToValue a) => Value (Arr f) -> f a b

instance MonadEval f => FromValue1 (Kleisli f) where
  type Arr (Kleisli f) = f
  fv x = Kleisli $ fromValue1 x


newtype Unsafe a b = Unsafe { runUnsafe :: a -> b }

instance FromValue1 Unsafe where
  type Arr Unsafe = EvalM
  fv x = Unsafe $ either error id . runEvalM <$> fromValue1 x


fromValue1 :: (ToValue a, FromValue r, MonadEval f) => Value f -> a -> f r
fromValue1 (VLam fv) a = do
  -- NOTE: unsafeToValueF here is safe, as long we know that a is not on the form (_ -> _).
  av <- delay . pure =<< unsafeToValueF a
  r <- fv av
  fromValue r
fromValue1 v _ = failed $ "fromValue1: Expected a lambda expression"


fromValue2 :: (ToValue a, ToValue b, FromValue r, MonadEval f) => Value f -> a -> b -> f r
fromValue2 (VLam fv) a b = do
  av <- (delay . pure) =<< unsafeToValueF a
  r <- fv av
  fromValue1 r b
fromValue2 v _ _ = failed $ "fromValue1: Expected a lambda expression"




-- | Like 'toValue, but interpret into an arbitrary Functor.
--
-- This is only defined for non-function types, as generally there is
-- generally no way to hoist a Value with lambdas. E.g. this can
-- not be proved/implemented:
--
--    hoistValue :: Functor f => (f ~> g) -> Value f -> Value g
--
-- This function is safe to call as long as there is no instance (ToValue (_ -> _))
--
unsafeToValueF :: forall f a. MonadEval f => ToValue a => a -> f (Value f)
unsafeToValueF = pure . fromFO . hoistValue nt . toFO . toValue
  where
    -- TODO this shoult be a N.T. from a free MonadEval to f.
    -- (EvalM is not quite that yet, but close!)
    nt :: EvalM ~> f
    nt = either failed pure . runEvalM

    toFO :: forall f . Functor f => Value f -> FirstOrderValue f
    toFO = go
      where
        go (VLamF t ()) = error "Please do not write (ToValue (a -> b))"
        go (VInt x) = VInt x
        go (VDbl x) = VDbl x
        go (VBool x) = VBool x
        go (VChar x) = VChar x
        go (VList x) = VList (go <$> x)
        go (VRecord x) = VRecord (goT <$> x)
        go (VVariant l x) = VVariant l (goT x)

        goT (Thunk f) = Thunk (go <$> f)

    fromFO :: forall f . Functor f => FirstOrderValue f -> Value f
    fromFO = go
      where
        go (VLamF t x) = absurd x
        go (VInt x) = VInt x
        go (VDbl x) = VDbl x
        go (VBool x) = VBool x
        go (VChar x) = VChar x
        go (VList x) = VList (go <$> x)
        go (VRecord x) = VRecord (goT <$> x)
        go (VVariant l x) = VVariant l (goT x)

        goT (Thunk f) = Thunk (go <$> f)







instance HasType a => HasType [a] where
    typeOf p = _TList $ typeOf (inside p)

instance ToValue a => ToValue [a] where
  toValue = VList . fmap toValue
instance FromValue a => FromValue [a] where
    fromValue (VList xs) = mapM fromValue xs
    fromValue v          = failfromValue "VList" v

-- TODO make up my mind re: Maybe...
instance ToValue a => ToValue (Maybe a) where
instance (HasType a) => HasType (Maybe a)
instance FromValue a => FromValue (Maybe a) where



-- We can't derive Void as its recursively defined...
instance HasType Void where
  typeOf _ = _TVariant _TRowEmpty
instance ToValue Void
instance FromValue Void

instance HasType ()
instance FromValue () where
    fromValue _ = pure ()
instance ToValue () where
  toValue _ = VRecord mempty


instance HasType LBS.ByteString where
  typeOf _ = _TBlob
instance ToValue LBS.ByteString where
  toValue = error "TODO ByteString"
instance FromValue LBS.ByteString where
  fromValue = error "TODO ByteString"

instance HasType T.Text where
  typeOf _ = _TText
instance ToValue T.Text where
  toValue = error "TODO Text"
instance FromValue T.Text where
  fromValue = error "TODO Text"

instance
#if __GLASGOW_HASKELL__ > 708
  {-# OVERLAPS #-}
#endif
  FromValue String where
    {- fromValue (VString s) = return s -}
    fromValue (VList xs)  = traverse getC xs
    fromValue v           = failfromValue "VString" v
      where

getC :: MonadEval f => Value qq -> f Char
getC (VChar c) = pure c
getC v = failfromValue "VString" v












-- TODO

instance HasType Ordering

instance (HasType a, HasType b) => HasType (Either a b)
instance (HasType a, HasType b) => HasType (a, b)
instance (HasType a, HasType b, HasType c) => HasType (a, b, c)
instance (HasType a, HasType b, HasType c, HasType d) => HasType (a, b, c, d)
instance (ToValue a, ToValue b) => ToValue (Either a b)
instance (FromValue a, FromValue b) => FromValue (Either a b)
instance (ToValue a, ToValue b) => ToValue (a, b)
instance (FromValue a, FromValue b) => FromValue (a, b)
-- TODO Vector/Set (as []), map as [Entry]








fromValueL :: MonadEval m => (Value qq -> m b) -> Value qq -> m [b]
fromValueL fromValue (VList xs) = mapM fromValue xs
fromValueL _         v          = failfromValue "VList" v




fromValueRTh (VRecord m) = return m
fromValueRTh v           = failfromValue "VRecord" v

failfromValue :: MonadEval f => String -> Value qq -> f a
failfromValue desc v = failed $ "Expected a " ++ desc ++
    ", but got: " ++ show (ppValue v)






-- TODO for testing...
data V1 a = V1 { s :: a } deriving (G.Generic, Show)
instance (HasType a) => HasType (V1 a)
instance (ToValue a) => ToValue (V1 a)
instance (FromValue a) => FromValue (V1 a)
data V2 a b = V2 { a :: a, b :: b } deriving (G.Generic, Show)
instance (HasType a, HasType b) => HasType (V2 a b)
instance (ToValue a, ToValue b) => ToValue (V2 a b)
instance (FromValue a, FromValue b) => FromValue (V2 a b)
data V3 a b c = V3 { x :: a, y :: b, z :: c } deriving (G.Generic, Show)
instance (HasType a, HasType b, HasType c) => HasType (V3 a b c)
instance (ToValue a, ToValue b, ToValue c) => ToValue (V3 a b c)
instance (FromValue a, FromValue b, FromValue c) => FromValue (V3 a b c)
data V4 a b c d = V4 { m :: a, n :: b, o :: c, p :: d } deriving (G.Generic, Show)
instance (HasType a, HasType b, HasType c, HasType d) => HasType (V4 a b c d)
instance (ToValue a, ToValue b, ToValue c, ToValue d) => ToValue (V4 a b c d)
instance (FromValue a, FromValue b, FromValue c, FromValue d) => FromValue (V4 a b c d)



data Choice0 deriving (G.Generic)
instance HasType Choice0
instance ToValue Choice0
instance FromValue Choice0
data Choice3 a b c = Choice3_1 a | Choice3_2 b | Choice3_3 c deriving (G.Generic, Show)
instance (HasType a, HasType b, HasType c) => HasType (Choice3 a b c)
instance (ToValue a, ToValue b, ToValue c) => ToValue (Choice3 a b c)
instance (FromValue a, FromValue b, FromValue c) => FromValue (Choice3 a b c)

-- TODO test
roundTrip :: (ToValue a, FromValue a) => a -> Either String a
roundTrip = undefined
{- roundTrip = runEvalM . fromValue . pureM . toValue -}
  {- where -}
    {- pureM = pure . runIdentity -}


-- FIXME debug
{- traceV :: Value -> Value -}
{- traceV x = trace (showR . runEvalM $ ppValue' x) x -}
showR (Right x) = show x
showR (Left e) = "<<Error:" <> show e <> ">>"


