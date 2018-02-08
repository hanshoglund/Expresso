{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# LANGUAGE TupleSections #-}

------------------------------------------------------------
-- Expresso API
--
-- These functions are currently used by the REPL and the test suite.
--
module Expresso
  ( module Expresso.Syntax
  , module Expresso.Eval
  , module Expresso.Type
  , module Expresso.TypeCheck
  , bind
  , eval
  , evalFile
  , evalString
  , evalString'
  , evalWithEnv
  , evalWithEnv'
  , showType
  , showValue
  , showValue'
  , typeOf
  , typeOfString
  , typeOfWithEnv
  ) where

import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)
import Control.Monad.IO.Class
import Data.Monoid
import Control.Applicative

import Expresso.Eval (EvalM, FromValue(..), Value, Value')
import Expresso.TypeCheck (TIState, initTIState)
import Expresso.Pretty (render)
import Expresso.Syntax
import Expresso.Type
import Expresso.Utils
import qualified Expresso.Eval as Eval
import qualified Expresso.TypeCheck as TypeCheck
import qualified Expresso.Parser as Parser

resolveImports :: ExpSI -> ExceptT String IO Exp
resolveImports esi = do
  es <- Parser.resolveImports_ esi
  -- TODO this runs evalStatic in IO...
  liftIO $ Eval.runEvalIO $ Eval.evalStatic es

runEvalE :: Eval.EvalPrimT IO a -> ExceptT String IO a
runEvalE = Eval.runEvIO'

typeOfWithEnv :: TypeEnv -> TIState -> ExpSI -> IO (Either String Type)
typeOfWithEnv tEnv tState ei = runExceptT $ do
    e <- resolveImports ei
    ExceptT $ return $ inferTypes tEnv tState e

typeOf :: ExpSI -> IO (Either String Type)
typeOf = typeOfWithEnv mempty initTIState

typeOfString :: String -> IO (Either String Type)
typeOfString str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ typeOf top

type Val = Eval.Value Eval.EvalIO
type Env = Eval.Env Eval.EvalIO

evalWithEnv
    :: FromValue a
    => (TypeEnv, TIState, Env)
    -> ExpSI
    -> IO (Either String a)
evalWithEnv env expr = runExceptT $ do
  v <- ExceptT $ evalWithEnv' env expr
  runEvalE $ Eval.fromValue v

evalWithEnv'
    :: (TypeEnv, TIState, Env)
    -> ExpSI
    -> IO (Either String Val)
evalWithEnv' (tEnv, tState, env) ei = runExceptT $ do
  e      <- resolveImports ei
  _sigma <- ExceptT . return $ inferTypes tEnv tState e
  runEvalE . (Eval.eval env {- >=> Eval.fromValue-}) $ e


eval :: FromValue a => ExpSI -> IO (Either String a)
eval = evalWithEnv (mempty, initTIState, mempty)

eval' :: ExpSI -> IO (Either String Val)
eval' = evalWithEnv' (mempty, initTIState, mempty)

evalFile :: FromValue a => FilePath -> IO (Either String a)
evalFile path = runExceptT $ do
    top <- ExceptT $ Parser.parse path <$> readFile path
    ExceptT $ eval top

evalString :: FromValue a => String -> IO (Either String a)
evalString str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ eval top

evalString' :: String -> IO (Either String Val)
evalString' str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ eval' top

-- used by the REPL to bind variables
bind
    :: (TypeEnv, TIState, Env)
    -> Bind Name
    -> ExpSI
    -> IO (TypeEnv, TIState, Env)
bind (tEnv, tState, env) b ei = do
    r  <- runExceptT $ resolveImports ei
    case r of
      Left x -> error x
      Right e -> do
        let (res'e, tState') =
                TypeCheck.runTI (TypeCheck.tcDecl (getAnn ei) b e) tEnv tState
        case res'e of
            Left err    -> error err
            Right tEnv' -> do
                thunk <- Eval.runEvalIO $ Eval.delay $ Eval.eval env e
                env'  <- Eval.runEvalIO $ Eval.bind env b thunk
                return (tEnv', tState', env')

inferTypes :: TypeEnv -> TIState -> Exp -> Either String Type
inferTypes tEnv tState e =
    fst $ TypeCheck.runTI (TypeCheck.typeCheck e) tEnv tState

showType :: Type -> String
showType = render . ppType

-- | This does *not* evaluate deeply
showValue :: Val -> String
showValue = render . Eval.ppValue

-- | This evaluates deeply
showValue' :: Val -> IO String
showValue' v = render <$> (Eval.runEvalIO $ Eval.ppValue' v)
