
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import qualified Data.ByteString.Lazy as LBS

import GHC.Generics
import GHC.TypeLits hiding (Text)
import Data.Proxy
import Data.Void
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad.Error

import Data.Vinyl

import Expresso hiding (typeOf) -- TODO resolve conflict
-- TODO reexport
import Expresso.Eval

main = defaultMain unitTests

unitTests = testGroup
  "End-to-end functional tests"
  [ letTests
  , lambdaTests
  , recordTests
  , variantTests
  , listTests
  , conversionTests
  , relationalTests
  , constraintTests
  , rankNTests
  , annotationTests

  , foreignTypeTests
  , foreignImportTests
  , foreignExportTests

  , lazyTests
  ]

letTests = testGroup
  "Let expressions"
  [ hasValue "let x = 1 in x" (1::Integer)
  , hasValue "let x = 1 in let y = 2 in x + y" (3::Integer)
  , hasValue "let x = 1; y = 2 in x + y" (3::Integer)

  {- , hasValue "let {..} = {inc = \\x -> x + 1} in inc 1" (2::Integer) -}
  {- , hasValue "let m = {inc = \\x -> x + 1} in m.inc 1" (2::Integer) -}

  {- , hasValue "let m = {id = \\x -> x} in {foo = [m.id 1], bar = m.id [1]}" -}
        {- $ toMap ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])] -}

  {- -- Record argument field-pun generalisation -}
  {- , hasValue "let {id} = {id = \\x -> x} in {foo = [id 1], bar = id [1]}" -}
        {- $ toMap ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])] -}
  {- , hasValue "let {..} = {id = \\x -> x} in {foo = [id 1], bar = id [1]}" -}
        {- $ toMap ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])] -}

    {- -- Num constraint violation -}
  {- , illTyped "let square = \\x -> x * x in {foo = square 1, bar = square [1]}" -}

  , hasValue "let {..} = {inc = x -> x + 1} in inc 1" (2::Integer)
  , hasValue "let m = {inc = x -> x + 1} in m.inc 1" (2::Integer)

  , hasValue "let m = {id = x -> x} in {foo = [m.id 1], bar = m.id [1]}"
        (re2 [1] [1] :: Re '[ '("bar",[Int]),'("foo",[Int]) ] )

  -- Record argument field-pun generalisation
  , hasValue "let {id} = {id = x -> x} in {foo = [id 1], bar = id [1]}"
        (re2 [1] [1] :: Re '[ '("bar",[Int]),'("foo",[Int]) ] )
  , hasValue "let {..} = {id = x -> x} in {foo = [id 1], bar = id [1]}"
        (re2 [1] [1] :: Re '[ '("bar",[Int]),'("foo",[Int]) ] )

    -- Num constraint violation
  , illTyped "let square = x -> x * x in {foo = square 1, bar = square [1]}"
  ]

lambdaTests = testGroup
  "Lambda expressions"
  [
    {- hasValue "(\\x -> \\y -> x + y) 1 2" (3::Integer) -}
  {- , hasValue "(\\x y -> x + y) 1 2" (3::Integer) -}
  {- , illTyped "\\x -> x x" -}
  {- , illTyped "let absorb = fix (\\r x -> r) in absorb" -}
  {- , illTyped "let create = fix (\\r x -> r x x) in create" -}
  {- ,  -}
    hasValue "(x -> y -> x + y) 1 2" (3::Integer)
  , hasValue "(x y -> x + y) 1 2" (3::Integer)
  , illTyped "x -> x x"
  , illTyped "let absorb = fix (r x -> r) in absorb"
  , illTyped "let create = fix (r x -> r x x) in create"
  ]


recordTests = testGroup
  "Record expressions"
  [ hasValue "({x, y} -> {x, y}) {x=1, y=2}" $
    (re2 1 2 :: Re ['("x", Integer),'("y", Integer)])

  , hasValue "{x = 1, y = 2}"
    (re2 1 2 :: Re ['("x", Integer),'("y", Integer)])
  , hasValue "(r -> { x = 1, y = 2 | r}) { z = 3 }"
    (re3 1 2 3 :: Re ['("x", Integer),'("y", Integer), '("z", Integer)])
  , hasValue "{ x = { y = { z = 42 }}}.x.y.z"
    (42::Integer)

  -- Row tail unification soundness
  , illTyped "r -> if True then { x = 1 | r } else { y = 2 | r }"

  , hasValue "({x, y} -> {x, y}) {x=1, y=2}"
    (re2 1 2 :: Re ['("x", Integer),'("y", Integer)])
  , hasValue "{x = 1, y = 2}"
    (re2 1 2 :: Re ['("x", Integer),'("y", Integer)])
  , hasValue "(r -> { x = 1, y = 2 | r}) { z = 3 }"
    (re3 1 2 3 :: Re ['("x", Integer),'("y", Integer), '("z", Integer)])
  , hasValue "{ x = { y = { z = 42 }}}.x.y.z" (42::Integer)

  -- Row tail unification soundness
  , illTyped "r -> if True then { x = 1 | r } else { y = 2 | r }"

  , illTyped "{ x = 2, x = 1 }.x" -- fails to typecheck
  , illTyped "{ x = 2 | { x = 1 }}.x" -- fails to typecheck
  , hasValue "{ x := 2, x = 1 }.x" (2::Integer)
  , hasValue "{ x := 2 | { x = 1 }}.x" (2::Integer)
  , hasValue "{| x = 1 |} {}"
    (re1 1 :: Re '[ '("x", Integer)])
  , hasValue "({| x = 1, y = 2 |} >> {| z = 3 |}) {}"
    (re3 1 2 3 :: Re ['("x", Integer),'("y", Integer), '("z", Integer)])
  , hasValue "({| x = 1, y = 2 |} >> {| x := 42 |}) {}"
    (re2 42 2 :: Re ['("x", Integer),'("y", Integer)])
  , illTyped "({| x = 1, y = 2 |} << {| x := 42 |}) {}" -- fails to typecheck
  , hasValue "({| x := 42, y = 2 |} << {| x = 1 |}) {}"
    (re2 42 2 :: Re ['("x", Integer),'("y", Integer)])

  -- large record
  , hasValue ("{ x = True }.x") True
  , hasValue ("{ x = 2" ++ concat [", x" ++ show n ++ " = 1" | n <- [1..129] ] ++ " }.x") (2::Integer)
  , hasValue "({| x := 42, y = 2 |} << {| x = 1 |}) {}"
    (re2 42 2 :: Re ['("x", Integer),'("y", Integer)])
  ]

variantTests = testGroup
  "Variant expressions"
  [ hasValue "case Foo 1 of { Foo x -> x + 1, Bar {x, y} -> x + y }"   (2::Integer)
  , hasValue "case Bar {x=1, y=2} of { Foo x -> x + 1, Bar {x, y} -> x + y }"   (3::Integer)
  , illTyped "case Baz{} of { Foo x -> x + 1, Bar {x, y} -> x + y }" -- fails to typecheck
  , hasValue "case Baz{} of { Foo x -> x + 1, Bar {x, y} -> x + y | otherwise -> 42 }"  (42::Integer)
  , illTyped "let f = s -> case s of { Foo x -> x + 1, Bar {x, y} -> x + y }; g = s -> f (<|Foo|> s) in g (Foo 1)" -- fails to typecheck
  , hasValue "let f = s -> case s of { Foo x -> x + 1, Bar {x, y} -> x + y }; g = s -> f (<|Foo|> s) in g (Bar{x=1, y=2})" (3::Integer)
  , hasValue "let f = s -> case s of { Foo x -> x + 1, Bar {x, y} -> x + y | otherwise -> 42 }; g = s -> f (<|Foo,Bar|> s) in g (Baz{})"  (42::Integer)
  , hasValue "case Foo 1 of { override Foo x -> x + 2 | s -> case s of { Foo x -> x + 1 }}" (3::Integer)
  , hasValue "case Foo 1 of { override Foo x -> x + 2, Foo x -> x + 1 }" (3::Integer)

  -- Fail in empty row case
  , illTyped "x -> case x of { A{} -> 1, B{} -> 2, A{} -> 3 }"
  -- Fail in row var case
  , illTyped "x -> <|A, B, A|> x"
  -- Failed row rewrite due to row constraints
  , illTyped ("let f = x -> case (<|A|> x) of { B{} -> 1, otherwise -> 2 }; " ++
              "let g = x -> case (<|B|> x) of { A{} -> 1, otherwise -> 2 } in " ++
              "x -> f x + f x")
  ]

conversionTests = testGroup
  "Type conversions"
  [

  -- Integer Char
    hasValue "charToInt (intToChar 2)" (2 :: Integer)
  , hasValue "intToChar 43" '+'

  -- [{}} Integer
  {- , hasValue "length [{},{}]" (2 :: Integer) -}
  {- , hasValue "repeat {} 2" (replicate 2 ()) -}
  -- [Char] Text
  , hasValue "\"ab\"" ("ab"::String) -- parse Haskell String as Expresso text for convenience
  , hasValue "\"ab\"" ("ab"::Text)

  -- [Char] Text
  , hasValue "packText ['f','o',intToChar 111]" ("foo" :: T.Text)
  , hasValue "packText (unpackText \"ab\")" ("ab" :: T.Text)

  -- [Integer] Blob
  , hasValue "packBlob [102,111,111]" ("foo" :: LBS.ByteString)
  , hasValue "unpackBlob (packBlob [102,110,111])" [102,110,111::Integer]

  , hasValue "foldr (u x -> x + 1) 0 [1,2,3]" (3 :: Integer)
  ]

listTests = testGroup
  "List expressions"
  [ hasValue "[1,2,3]" [1::Integer,2,3]
  , illTyped "[1,True]"
  ]

relationalTests = testGroup
  "Relational expressions"
  [ hasValue "(1 == 2)" False
  , hasValue "(\"foo\" == \"bar\")" False
  , hasValue "\"a\" < \"b\"" True
  , hasValue "1/=2" True
  , illTyped "1 == 2 == 3"
  , hasValue "{x = 1, y = True} == {y = True, x = 1}" True -- field order should not matter
  , illTyped "{x = 1, y = True} > {y = True, x = 1}" -- cannot compare records for ordering
  , illTyped "Foo 1 > Bar{}" -- cannot compare variants for ordering
  , hasValue "[1,2,3] == [1,2,3]" True -- lists can be compared for equality
  , hasValue "[1,2,3] >= [1,2,2]" True -- lists can be compared for ordering
  , hasValue "Just 1 == Just 1" True -- maybe can be compared for equality
  , hasValue "True&&True"   True
  , hasValue "True||False"  True
  ]

constraintTests = testGroup
  "Constraint violations"
  [ illTyped "show { x = \"test\", y = Just (x -> x) }"
  , illTyped "{ x = 2 } > { x = 1}"
  , illTyped "let f = x y -> x + y in f True False"
  ]


lazyTests = testGroup
  "Lazy evaluation tests using error primitive"
  [ hasValue "(import \"Prelude.x\").maybe (error \"bang!\") (x -> x == 42) (Just 42)" True
  , hasValue "{ x = error \"boom!\", y = 42 }.y" (42::Integer)
  , hasValue "case Bar (error \"fizzle!\") of { Foo{} -> 0 | otherwise -> 42 }" (42::Integer)
  {- , failsAtRuntime "error \"_|_\"" -}
  ]


rankNTests = testGroup
  "Rank-N polymorphism"
  [ hasValue
         "let f = (g : forall a. a -> a) -> {l = g True, r = g 1} in f (x -> x) == {l = True, r = 1}" True
  , hasValue
         "let k = f g x -> f (g x) in let t = k ({} -> True) (x -> {}) False in let xx = k (a -> {}) (x -> {}) in t" True

  , hasValue "let f = (g : forall a. a -> a) -> {l = g True, r = g 1} in f (x -> x) == {l = True, r = 1}" True
  , hasValue "let f = g -> {l = g True, r = g 1} : (forall a. a -> a) -> {l : Bool, r : Int } in f (x -> x) == {l = True, r = 1}" True
  , hasValue
         "let f = (m : forall a. { reverse : [a] -> [a] |_}) -> {l = m.reverse [True, False], r = m.reverse (unpackText \"abc\") } in f (import \"Prelude.x\") == {l = [False, True], r = unpackText \"cba\"}" True
  ]

annotationTests = testGroup
  "Type annotations"
  [ hasValue
         "let x = (error \"_|_\" : forall a. a -> {foo : {}, z : a, bar : Double}) in True" True
  , hasValue
         "let x = (error \"_|_\" : forall a. a -> {foo : Text, z : a, bar : Double}) in True" True
  , hasValue
         "let x = (error \"_|_\" : forall a. a -> {foo : Blob, z : a, bar : Double}) in True" True


  , wellTyped
         "(error\"_|_\" : forall r.(r\\L) => <L:{}   | r>) : <L:{},R:{}>"
  , illTyped
         "(error\"_|_\" : forall r.(r\\L) => <L:Bool | r>) : <L:{},R:{}>"


  {- , "<>"                `isSubtypeOf`         "Int" -}
  , "Int"               `isSubtypeOf`         "forall a.a"
  , "forall a.{x:a,y:Int}"
                        `isSubtypeOf`         "forall a b.{x:a,y:b}"

  , "forall a b.{x:a,y:b}"
                        `isNotSubtypeOf`      "forall a b.{x:a,y:Int}"


  , "{foo:Int}"         `isSubtypeOf`         "forall r.(r\\foo) =>     {foo:Int|r}"
  , "<L:{}>"            `isSubtypeOf`         "forall r.(r\\L)   =>     <L:{}|r>"






  , "<L:{},R:{}>"       `isSubtypeOf`         "forall r.(r\\L) => <L:{}|r>"
  , "{foo:Int,bar:Int}" `isSubtypeOf`         "forall r.(r\\foo) => {foo:Int|r}"
  , "{foo:Int,bar:Int}" `isNotSubtypeOf`      "{foo:Int}"

  -- TODO check variance works...

  , "{foo:Int} -> <L:Int>"
    `isSubtypeOf`
    "forall r r1. (r\\foo, r1\\L) => {foo: Int|r} -> <L:Int | r1>"

  , "{foo:Int} -> <L:Int>"
    `isSubtypeOf`
    "forall a r r1. (r\\foo, r1\\L) => {foo : a | r} -> <L : a | r1>"

  , "<L:{},R:{}>"       `isSubtypeOf`         "forall r.(r\\L) => <L:{}|r>"
  , "forall a.a"        `isSubtypeOf`         "forall a.a"


  -- In a client/server setting, wer can think of the server as providing a single funtion to be called
  -- We want that function to be a supertype of whatever the client expects


  -- Server allowing client to handle returns case L2 that will never be sent
  , "Int -> <L: Int, R : Char>"
        `isSubtypeOf`
    "forall r. (r\\R) => (Int -> <R : Char | r>)"
  , "Int -> <L: Int, R : Char>"
        `isSubtypeOf`
    "forall r. (r\\L, r\\R) => (Int -> <L: Int, R : Char | r>)"
  , "Int -> <L: Int, R : Char>"
        `isNotSubtypeOf`
    "Int -> <R : Char>"

  -- Server allowing client to pass parameter that will never be used
  , "{x:Int,y:Bool} -> Int"
        `isSubtypeOf`
    "forall r . (r\\x) => {x:Int | r} -> Int"
  -- Same client with an upgraded server using Bool
  , "{x:Int,y:Bool} -> Int"
        `isSubtypeOf`
    "forall r . (r\\x, r\\y) => {x:Int, y:Bool | r} -> Int"
  -- Same client with an incomaptible server, not allowed!
  , "{x:Int,y:Bool} -> Int"
        `isNotSubtypeOf`
    "forall r . (r\\x, r\\y) => {x:Int, y:Int | r} -> Int"

  -- The *normal* case:
  --   Reciever accepts open records/closed variants (e.g. handle known fields, ignore rests, refuse to handle unknown cases)
  --   Sender provides closed records/open variants
  --
  -- When modelling client server as a function, we have on LHS client sending, on RHS server sending

  -- OK: client sending an extra field
  -- OK: client recieving an extra field
  -- BAD: server missing a field in request
  -- BAD: server sending a case not handled by client
  -- OK: server sending fewer cases than expected by client


  -- For *infrastructure* we are not restricted to client/server, instead the client sends a complete value
  -- We are "fitting" the client type into a "hole" of some shape
  --
  -- The client type will normally be inferred and should be the larger type
  -- The infrastructure will expect a single concrete type that the client must satisfy


  -- OK: Client and infra is the same
  -- OK: Client and server have diverged, but are compatible
  -- BAD: Client and server no longer compatible
  ]



instance (f ~ ElField) => HasType (Rec f '[]) where
  typeOf _ = _TRecord $ _TRowEmpty
instance (f ~ ElField) => HasType (Rec f ('(k, v) : rs)) where
  typeOf p = _TRecord $ _TRowEmpty

instance (f ~ ElField) => FromValue (Rec f '[]) where
  fromValue _ = pure RNil

instance (f ~ ElField, KnownSymbol k, FromValue v, FromValue (Rec f rs)) => FromValue (Rec f ('(k, v) : rs)) where
  fromValue v = do
    case v of
      VRecord r -> case HashMap.lookup k r of
        Just x -> do
          v <- fromValue =<< force x
          r <- fromValue (VRecord r)
          pure $ rCons kp v r
        Nothing -> failed $ "bad record, no '" -- FIXME ++ k ++ "'"
      v -> failed $ "not a record: " -- FIXME ++ show v
    where
      k = symbolVal kp
      kp = (undefined :: F k)

fi :: FI s a -> FieldRec '[ '(s, a) ]
fi (FI x) = SField =: x

data FI :: Symbol -> * -> * where
  FI :: KnownSymbol s => a -> FI s a

instance Functor (FI s) where
  fmap f (FI x) = FI (f x)

instance KnownSymbol s => Applicative (FI s) where
  pure x = FI x
  FI f <*> FI x = FI (f x)

type Re = FieldRec

re1 x = pure x & RNil
re2 x y = pure x & re1 y
re3 x y z = pure x & re2 y z


{- r1 :: FieldRec '[ '("foo", Bool) ] -}
{- r1 = (SField :: SField '("foo",Bool)) =: True -}

{- r2 :: Rec ElField '[ '("foo", Bool), '("bar", Bool)] -}
{- r2 = rec (f::F"foo") True <+> rec (f::F"bar") False -}


a & b = fi a <+> b
infixr 1 &
{- infixr 7 ==> -}

rCons :: KnownSymbol t => proxy t -> a -> FieldRec rs -> FieldRec ('(t, a) : rs)
rCons _ v rs = Field v :& rs

{- rec :: KnownSymbol t => proxy t -> a -> FieldRec '[ '(t, a) ] -}
{- rec _ = (SField =:) -}



{- (==>) :: KnownSymbol s => F s -> a -> FI s a -}
{- _ ==> b = FI b -}


data F :: Symbol -> * where
{- f :: F s -}
{- f = undefined -}

-- Marshalling
data Rat = Rat { nom :: Integer, denom :: Integer } | Simple Integer deriving (Generic)

instance HasType Rat
instance FromValue Rat
instance ToValue Rat

newtype ANewType = ANewType { runANewType :: Int } deriving Generic

instance HasType ANewType
instance FromValue ANewType
instance ToValue ANewType

foreignTypeTests = testGroup
  "Foreign types"
  [ hasType (xx :: Proxy Int) "Int"
  , hasType (xx :: Proxy Integer) "Int"
  , hasType (xx :: Proxy Double) "Double"
  , hasType (xx :: Proxy Text) "Text"
  , hasType (xx :: Proxy String) "Text"
  , hasType (xx :: Proxy [(Int,Bool)])
      "[{_1 : Int, _2 : Bool}]"
    -- or?:
    -- "[(Int,Bool)]"
  -- TODO support Char?
  -- TODO add Text
  , doesNotHaveType (xx :: Proxy Int) "Bool"

  , hasType (xx :: Proxy ()) "{}"
  , hasType (xx :: Proxy Void) "<>"
  , hasType (xx :: Proxy (Either () ())) "<Left : {}, Right : {}>"
  , hasType (xx :: Proxy (Maybe Int)) "<Just : Int, Nothing : {}>"
  {- , hasType (xx :: Proxy (Map String Bool)) "" -} -- TODO add maps as [{key:k,value:v)]
  , hasType (xx :: Proxy (Ordering)) "<EQ : {}, GT : {}, LT : {}>"
  , hasType (xx :: Proxy (Rat)) "<Rat : {denom : Int, nom : Int}, Simple : Int>"

  -- TODO treat ANewType as <ANewType : Int> instead?
  --
  -- No: This complicates the representation of things isomorphic to (), (a,b) etc
  -- Tagging can easily be provided by overriding HasType anyway
  , hasType (xx :: Proxy (ANewType)) "Int"
  , hasType (xx :: Proxy (Int -> EvalM Int)) "Int -> Int"
  , hasType (xx :: Proxy (Int -> EvalM (Int, Bool)))
      "Int -> {_1 : Int, _2 : Bool}"
  , hasType (xx :: Proxy ((), Int -> EvalM Int, String -> EvalM Bool))
      "{_1 : {}, _2 : Int -> Int, _3 : Text -> Bool}"
  ]

foreignImportTests = testGroup
  "Foreign import (Haskell to Expresso)"
  [ isValue "1" (1 :: Int)
  , isValue "1" (1 :: Integer)
  , isValue "True" True
  , isValue "2.5" (2.5 :: Double)
  , isValue "\"hello\"" ("hello" :: String)
  , isValue "{}" ()
  , isValue "Just 2" (Just (2 :: Int))
  ]

foreignExportTests = testGroup
  "Foreign export (Expresso to Haskell)"
  [ hasValue "1" (1 :: Int)
  , hasValue "1" (1 :: Integer)
  , hasValue "True" True
  , hasValue "2.5" (2.5 :: Double)
  , hasValue "\"hello\"" ("hello"::String)
  , hasValue "{}" ()
  , hasValue "Just 2" (Just (2 :: Int))

  , hasValueF "x -> x" (2 :: Int) (2 :: Int)
  , hasValueF2 "x y -> x" (2 :: Int) (3 :: Int) (2 :: Int)
  , hasValueF2 "x y -> y" (2 :: Int) (3 :: Int) (3 :: Int)
  ]

xx :: Proxy a
xx = error "Do not evaluate"

hasType :: HasType a => Proxy a -> String -> TestTree
hasType hsTy expected = testCase caseStr $
  assertEqual "" expected (show $ ppType $ typeOf hsTy)
  where
    caseStr = show hsTy ++ " " ++ show expected

doesNotHaveType :: HasType a => Proxy a -> String -> TestTree
doesNotHaveType hsTy expected = testCase caseStr $
  if expected == actual
    then assertFailure $ "The Haskell type " ++ expected ++ " should not correspond to " ++ actual
    else assertTrue
  where
    actual = show $ ppType $ typeOf hsTy
    caseStr = show hsTy ++ " " ++ show expected

-- | Test that a given HS value can be imported to Expresso.
isValue :: ToValue a => String -> a -> TestTree
isValue expected hsVal = testCase caseStr $
  assertEqual "" expected actual
  where
    actual = show $ toValue hsVal
    caseStr = expected


-- | Test that a given Expresso expression can be evaluated and exported to Haskell.
hasValue :: (Eq a, Show a, FromValue a) => String -> a -> TestTree
hasValue str = hasValue' str pure


-- | Test that a given Expresso expression evalutates to a function, which when applied
-- to the given value returns the given result.
hasValueF :: (Eq r, Show r, FromValue r, ToValue a) => String -> a -> r -> TestTree
hasValueF str a expected = testCase str $ do
  result <- evalString' str
  case result of
    Left err -> assertFailure err
    Right f -> do
      actual  <- runEvalIO $ fromValue1 f a
      assertEqual "" expected actual

hasValueF2 :: (Eq r, Show r, FromValue r, ToValue a, ToValue b) => String -> a -> b -> r -> TestTree
hasValueF2 str a b expected = testCase str $ do
  result <- evalString' str
  case result of
    Left err -> assertFailure err
    Right f -> do
      actual  <- runEvalIO $ fromValue2 f a b
      assertEqual "" expected actual


hasValue' :: (Eq b, Show b, FromValue a) => String -> (a -> EvalIO b) -> b -> TestTree
hasValue' str f expected = testCase str $ do
    result <- evalString str
    case result of
        Left err     -> assertFailure err
        Right x      -> do
          actual <- runEvalIO $ f x
          assertEqual "" expected actual

isSubtypeOf :: String -> String -> TestTree
isSubtypeOf t1 t2 = wellTyped $
  "(error\"_|_\" : "++t2++") : "++t1++""

isNotSubtypeOf :: String -> String -> TestTree
isNotSubtypeOf t1 t2 = illTyped $
  "(error\"_|_\" : "++t2++") : "++t1++""

wellTyped :: String -> TestTree
wellTyped str = testCase str $ do
    sch'e <- typeOfString str
    case sch'e of
        Left e  -> assertFailure $ "Should type-check, but got: " ++ show e
        Right _ -> assertTrue

illTyped :: String -> TestTree
illTyped str = testCase str $ do
    sch'e <- typeOfString str
    case sch'e of
        Left _    -> assertTrue
        Right sch -> assertFailure $ "Should not type-check, but got: " ++ showType sch

assertTrue = return ()

-- TODO
-- Do not export RT representation from Eval (move vinyl stuff)
-- More cleanup: doc stuff, rename unsafeFromV...
-- Make lists non-strict
-- Add/test typeOfValue
-- separate user errors from compile/TC errors...


-- Static evaluation
--   Rewrite an AST containing
--
--       static (Web { url = "http://", format = Zip {}, hash = Sha256 "167612736767a67aaaaba7" })
--        :  <Static : <File : {url : [Char], format : <Zip : {} >, hash : <Sha256 : [Char] >} > >
--
--       static (Local { File { path= "/foo/bar" }})
--
--       static (Local { Directory { path= "/foo/bar" }})
--
--       static (Local { ForgeBinary { name = "scl-ui" } })
--




