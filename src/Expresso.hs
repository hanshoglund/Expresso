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
  , evalWithEnv
  , showType
  , showValue
  , showValue'
  , typeOf
  , typeOfString
  , typeOfWithEnv
  ) where

import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)

import Expresso.Eval (Env, EvalM, HasValue(..), Value(..), runEvalM)
import Expresso.TypeCheck (TIState, initTIState)
import Expresso.Pretty (render)
import Expresso.Syntax
import Expresso.Type
import Expresso.Utils
import qualified Expresso.Eval as Eval
import qualified Expresso.TypeCheck as TypeCheck
import qualified Expresso.Parser as Parser


typeOfWithEnv :: TypeEnv -> TIState -> ExpI -> IO (Either String Type)
typeOfWithEnv tEnv tState ei = runExceptT $ do
    e <- Parser.resolveImports ei
    ExceptT $ return $ inferTypes tEnv tState e

typeOf :: ExpI -> IO (Either String Type)
typeOf = typeOfWithEnv mempty initTIState

typeOfString :: String -> IO (Either String Type)
typeOfString str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ typeOf top

evalWithEnv
    :: HasValue a
    => (TypeEnv, TIState, Env)
    -> ExpI
    -> IO (Either String a)
evalWithEnv (tEnv, tState, env) ei = runExceptT $ do
  e      <- Parser.resolveImports ei
  _sigma <- ExceptT . return $ inferTypes tEnv tState e
  ExceptT $ runEvalM . (Eval.eval env >=> Eval.proj) $ e

eval :: HasValue a => ExpI -> IO (Either String a)
eval = evalWithEnv (mempty, initTIState, mempty)

evalFile :: HasValue a => FilePath -> IO (Either String a)
evalFile path = runExceptT $ do
    top <- ExceptT $ Parser.parse path <$> readFile path
    ExceptT $ eval top

evalString :: HasValue a => String -> IO (Either String a)
evalString str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ eval top

-- used by the REPL to bind variables
bind
    :: (TypeEnv, TIState, Env)
    -> Bind Name
    -> ExpI
    -> EvalM (TypeEnv, TIState, Env)
bind (tEnv, tState, env) b ei = do
    e     <- Parser.resolveImports ei
    let (res'e, tState') =
            TypeCheck.runTI (TypeCheck.tcDecl (getAnn ei) b e) tEnv tState
    case res'e of
        Left err    -> throwError err
        Right tEnv' -> do
            thunk <- Eval.mkThunk $ Eval.eval env e
            env'  <- Eval.bind env b thunk
            return (tEnv', tState', env')

inferTypes :: TypeEnv -> TIState -> Exp -> Either String Type
inferTypes tEnv tState e =
    fst $ TypeCheck.runTI (TypeCheck.typeCheck e) tEnv tState

showType :: Type -> String
showType = render . ppType

-- | This does *not* evaluate deeply
showValue :: Value -> String
showValue = render . Eval.ppValue

-- | This evaluates deeply
showValue' :: Value -> IO String
showValue' v = either id render <$> (runEvalM $ Eval.ppValue' v)
