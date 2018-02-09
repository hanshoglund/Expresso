{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Expresso.Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Data.Maybe
import Data.Monoid
import Text.Parsec hiding (many, optional, parse, (<|>))
import Text.Parsec.Language (emptyDef)
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as P
import qualified Text.Parsec.Token as P

import Expresso.Pretty (Doc, (<+>), render, parensList, text, dquotes, vcat)
import Expresso.Syntax
import Expresso.Type
import Expresso.Utils

------------------------------------------------------------
-- Resolve imports


resolveImports_ :: ExpSI -> ExceptT String IO ExpS
resolveImports_ = cataM alg where
  alg (InR (Constant (Import path)) :*: _) = do
      res <- ExceptT $ readFile path >>= return . parse path
      resolveImports_ res
  alg (InL e :*: pos) = return $ Fix (e :*: pos)
  alg _ = error "safe: GHC pattern synonym limitation"

------------------------------------------------------------
-- Parser

parse :: SourceName -> String -> Either String ExpSI
parse src = showError . P.parse (whiteSpace *> pExp <* P.eof) src

pExp     = addTypeAnnot
       <$> getPosition
       <*> pExp'
       <*> optional (reservedOp ":" *> pTypeAnn)

addTypeAnnot pos e (Just t) = withPos pos (EAnn e t)
addTypeAnnot _   e Nothing  = e

pExp'    = pImport
       <|> pStatic
       <|> pLam
       <|> pAnnLam
       <|> pLet
       <|> pCond
       <|> pCase
       <|> pOpExp
       <?> "expression"

pImport  = mkImport
       <$> getPosition
       <*> (reserved "import" *> stringLiteral)
       <?> "import"

pStatic  = mkStatic
       <$> getPosition
       <*> (reserved "static" *> pExp)
       <?> "static"

pLet     = reserved "let" *>
           (flip (foldr mkLet) <$> (semiSep1 ((,) <$> getPosition <*> pLetDecl))
                               <*> (reserved "in" *> pExp))
           <?> "let expression"

pLetDecl = (,) <$> pLetBind
               <*> (reservedOp "=" *> pExp <* whiteSpace)

pLam     = mkLam
       <$> getPosition
       <*> try (many1 pBind <* reservedOp "->" <* whiteSpace)
       <*> pExp'
       <?> "lambda expression"

pAnnLam  = mkAnnLam
       <$> getPosition
       <*> try (many1 pAnnBind <* reservedOp "->" <* whiteSpace)
       <*> pExp'
       <?> "lambda expression with type annotated argument"

pAnnBind = parens $ (,) <$> pBind <*> (reservedOp ":" *> pTypeAnn)

pAtom    = pPrim <|> try pVar <|> parens (pSection <|> pExp)

pSection = pSigSection

pSigSection = mkSigSection <$> getPosition <*> (reservedOp ":" *> pTypeAnn)
{- >>>>>>> tim/master -}

pVar     = mkVar <$> getPosition <*> identifier

pPrim    = pNumber           <|>
           pBool             <|>
           pChar             <|>
           {- pMaybe            <|> -}
           pDifferenceRecord <|>
           pRecord           <|>
           pVariant          <|>
           pVariantEmbed     <|>
           pList             <|>
           pString           <|>
           pPrimFun

pCond    = (\pos -> mkTertiaryOp pos Cond)
               <$> getPosition
               <*> (reserved "if"   *> pExp)
               <*> (reserved "then" *> pExp)
               <*> (reserved "else" *> pExp)
               <?> "if expression"

pOpExp   = P.buildExpressionParser opTable pApp

-- NB: assumes "-1" and "+1" are not valid terms
pApp     = mkApp <$> getPosition <*> pTerm <*> many pTerm

pTerm    = mkRecordRestrict
        <$> getPosition
        <*> ((\pos -> foldl (mkRecordSelect pos))
            <$> getPosition
            <*> pAtom
            <*> try (many pSelect))
        <*> optional (reservedOp "\\" *> identifier)

opTable  = [ [ prefix "-" Neg
             ]
           , [ binary ">>" FwdComp        P.AssocRight
             , binary "<<" BwdComp        P.AssocRight
             ]
           , [ binary "*" (ArithPrim Mul) P.AssocLeft
             , binary "/" (ArithPrim Div) P.AssocLeft
             ]
           , [ binary "+" (ArithPrim Add) P.AssocLeft
             , binary "-" (ArithPrim Sub) P.AssocLeft
             ]
           , [ binary "++" ListAppend     P.AssocLeft
             , binary "::" ListCons       P.AssocRight
             ]
           , [ binary "==" Eq             P.AssocLeft
             , binary "/=" NEq            P.AssocLeft
             , binary ">"  (RelPrim RGT)  P.AssocLeft
             , binary ">=" (RelPrim RGTE) P.AssocLeft
             , binary "<"  (RelPrim RLT)  P.AssocLeft
             , binary "<=" (RelPrim RLTE) P.AssocLeft
             ]
           , [ binary "&&" And            P.AssocRight
             ]
           , [ binary "||" Or             P.AssocRight
             ]
           ]

pPrimFun = msum
  [ fun "error"   ErrorPrim
  , fun "trace"   Trace
  , fun "show"    Show
  , fun "not"     Not
  {- , fun "maybe"   MaybePrim -}
  , fun "foldr"   ListFoldr
  , fun "null"    ListNull
  , fun "fix"     FixPrim
  , fun "double"  Double
  , fun "floor"   Floor
  , fun "ceiling" Ceiling
  , fun "abs"     Abs
  , fun "mod"     Mod
  , fun "absurd"  Absurd

  , fun "charToInt" CharToInt
  , fun "intToChar" IntToChar

  , fun "packBlob"    PackBlob
  , fun "unpackBlob"  UnpackBlob
  , fun "packText"    PackText
  , fun "unpackText"  UnpackText
  ]
  where
    fun sym prim = reserved sym *> ((\pos -> mkPrim pos prim) <$> getPosition)

binary sym prim =
    P.Infix $ reservedOp sym *> ((\pos -> mkBinOp pos prim) <$> getPosition)
prefix sym prim =
    P.Prefix $ reservedOp sym *> ((\pos -> mkUnaryOp pos prim) <$> getPosition)

pSelect = reservedOp "." *> identifier

pNumber = (\pos -> either (mkInteger pos) (mkDouble pos))
       <$> getPosition
       <*> naturalOrFloat

pBool = (\pos -> mkPrim pos . Bool)
     <$> getPosition
     <*> (reserved "True"  *> pure True <|>
          reserved "False" *> pure False)

pChar = (\pos -> mkPrim pos . Char)
     <$> getPosition
     <*> charLiteral

pString = (\pos -> mkPrim pos . Text . T.pack)
       <$> getPosition
       <*> stringLiteral

pBind = Arg <$> identifier
    <|> RecArg <$> pFieldPuns

pLetBind = try (RecWildcard <$ reservedOp "{..}") <|> pBind

pFieldPuns = braces $ pRecordLabel `sepBy` comma

data Entry = Extend Label ExpSI | Update Label ExpSI

pRecord = (\pos -> fromMaybe (mkRecordEmpty pos))
       <$> getPosition
       <*> (braces $ optionMaybe pRecordBody)

pRecordBody = mkRecordExtend <$> getPosition <*> pRecordEntry <*> pRest
  where
    pRest = (comma          *> pRecordBody)  <|>
            (reservedOp "|" *> pExp)         <|>
            (mkRecordEmpty <$> getPosition)

pDifferenceRecord = mkDifferenceRecord
    <$> getPosition
    <*> (try (reservedOp "{|") *> (pRecordEntry `sepBy1` comma)
           <* reservedOp "|}")

mkDifferenceRecord :: Pos -> [Entry] -> ExpSI
mkDifferenceRecord pos entries =
    withPos pos $ ELam (Arg "#r") $
        foldr (mkRecordExtend pos) (withPos pos $ EVar "#r") entries

pRecordEntry =
    try (Extend <$> pRecordLabel <*> (reservedOp "=" *> pExp))  <|>
    try (Update <$> pRecordLabel <*> (reservedOp ":=" *> pExp)) <|>
    mkFieldPun <$> getPosition <*> pRecordLabel

pRecordLabel  = lowerIdentifier

pVariant = mkVariant <$> getPosition <*> pVariantLabel

pVariantEmbed = mkVariantEmbed
             <$> getPosition
             <*> (try (reservedOp "<|") *> (pEmbedEntry `sepBy1` comma)
                    <* reservedOp "|>")
             <?> "variant embed expression"
    where
      pEmbedEntry = (,) <$> getPosition <*> pVariantLabel

pCase = mkCase <$> getPosition
               <*> (reserved "case" *> pApp <* reserved "of")
               <*> (braces pCaseBody)
               <?> "case expression"

pCaseBody = mkCaseAlt <$> getPosition <*> pCaseAlt <*> pRest
  where
    pRest = (comma          *> pCaseBody)   <|>
            (reservedOp "|" *> pExp)        <|>
            (\pos -> mkPrim pos Absurd) <$> getPosition

pCaseAlt =
    (try (Extend <$> pVariantLabel
                 <*> (whiteSpace *> pLam)) <|>
     try (Update <$> (reserved "override" *> pVariantLabel)
                 <*> (whiteSpace *> pLam)))
    <?> "case alternative"

pVariantLabel = upperIdentifier

{- pMaybe =  (\pos -> mkPrim pos JustPrim)    <$> getPosition <* reserved "Just" -}
      {- <|> (\pos -> mkPrim pos NothingPrim) <$> getPosition <* reserved "Nothing" -}

pList = brackets pListBody
  where
    pListBody = (\pos -> foldr mkListCons (mkListEmpty pos))
        <$> getPosition
        <*> ((,) <$> getPosition <*> pExp) `sepBy` comma
        <?> "list expression"

mkImport :: Pos -> FilePath -> ExpSI
mkImport pos path = withAnn pos $ InR $ K $ Import path

mkStatic :: Pos -> ExpSI -> ExpSI
mkStatic pos exp = withAnn pos $ InL $ InR $ K $ Static (destatic exp)

-- TODO generalize parser to get parse errors for nested static expressions
-- As we run all static expressions at compile time, it's not too terrible
destatic :: ExpSI -> Exp
destatic = cata g
  where
    g :: ExpFSI Exp -> Exp
    g (InR (K (Import _)) :*: pos) = error $ show pos <> ": import statements are not allowed in static blocks"
    g (InL (InR (K (Static _))) :*: pos) = error $ show pos <> ": nested static blocks are not allowed"
    g (InL (InL e) :*: pos) = Fix (e :*: pos)
    g _ = error "safe: not detected due to GHC pattern synonym limitation 4"

mkInteger :: Pos -> Integer -> ExpSI
mkInteger pos = mkPrim pos . Int

mkDouble :: Pos -> Double -> ExpSI
mkDouble pos = mkPrim pos . Dbl

mkCase :: Pos -> ExpSI -> ExpSI -> ExpSI
mkCase pos scrutinee caseF = mkApp pos caseF [scrutinee]

mkCaseAlt :: Pos -> Entry -> ExpSI -> ExpSI
mkCaseAlt pos (Extend l altLamE) contE =
    mkApp pos (mkPrim pos $ VariantElim l) [altLamE, contE]
mkCaseAlt pos (Update l altLamE) contE =
    mkApp pos (mkPrim pos $ VariantElim l)
          [ altLamE
          , mkLam pos [Arg "#r"]
                      (mkApp pos contE [mkEmbed $ withPos pos $ EVar "#r"])
          ]
  where
    mkEmbed e = mkApp pos (mkPrim pos $ VariantEmbed l) [e]

mkVariant :: Pos -> Label -> ExpSI
mkVariant pos l = mkPrim pos $ VariantInject l

mkVariantEmbed :: Pos -> [(Pos , Label)] -> ExpSI
mkVariantEmbed pos ls =
    withPos pos $ ELam (Arg "#r") $
        foldr f (withPos pos $ EVar "#r") ls
  where
    f (pos, l) k = mkApp pos (mkPrim pos $ VariantEmbed l) [k]

mkLam :: Pos -> [Bind Name] -> ExpSI -> ExpSI
mkLam pos bs e =
    foldr (\b e -> withPos pos (ELam b e)) e bs

mkAnnLam :: Pos -> [(Bind Name, Type)] -> ExpSI -> ExpSI
mkAnnLam pos bs e =
    foldr (\(b, t) e -> withPos pos (EAnnLam b t e)) e bs

-- | signature section
--   (:T) becomes (x -> x : T -> T)
mkSigSection :: Pos -> Type -> ExpSI
mkSigSection pos ty =
    withPos pos $ EAnn (mkLam pos [Arg "x"] (mkVar pos "x")) ty'
  where
    ty' = case ty of
        (Fix (TForAllF tvs t :*: K pos)) ->
            withAnn pos (TForAllF tvs (withAnn pos (TFunF t t)))
        t -> withAnn (getAnn t) (TFunF t t)

mkVar :: Pos -> Name -> ExpSI
mkVar pos name = withPos pos (EVar name)

mkLet :: (Pos, (Bind Name, ExpSI)) -> ExpSI -> ExpSI
mkLet (pos, (b, e1)) e2 = withPos pos (ELet b e1 e2)

mkTertiaryOp :: Pos -> Prim -> ExpSI -> ExpSI -> ExpSI -> ExpSI
mkTertiaryOp pos p x y z = mkApp pos (mkPrim pos p) [x, y, z]

mkBinOp :: Pos -> Prim -> ExpSI -> ExpSI -> ExpSI
mkBinOp pos p x y = mkApp pos (mkPrim pos p) [x, y]

mkUnaryOp  :: Pos -> Prim -> ExpSI -> ExpSI
mkUnaryOp pos p x = mkApp pos (mkPrim pos p) [x]

mkRecordSelect :: Pos -> ExpSI -> Label -> ExpSI
mkRecordSelect pos r l = mkApp pos (mkPrim pos $ RecordSelect l) [r]

mkRecordExtend :: Pos -> Entry -> ExpSI -> ExpSI
mkRecordExtend pos (Extend l e) r =
    mkApp pos (mkPrim pos $ RecordExtend l) [e, r]
mkRecordExtend pos (Update l e) r =
    mkApp pos (mkPrim pos $ RecordExtend l) [e, mkRecordRestrict pos r $ Just l]

mkRecordEmpty :: Pos -> ExpSI
mkRecordEmpty pos = mkPrim pos RecordEmpty

mkRecordRestrict :: Pos -> ExpSI -> Maybe Label -> ExpSI
mkRecordRestrict pos e = maybe e $ \l -> mkApp pos (mkPrim pos $ RecordRestrict l) [e]

mkFieldPun :: Pos -> Label -> Entry
mkFieldPun pos l = Extend l (withPos pos $ EVar l)

mkListCons :: (Pos, ExpSI) -> ExpSI -> ExpSI
mkListCons (pos, x) xs = mkApp pos (mkPrim pos ListCons) [x, xs]

mkListEmpty :: Pos -> ExpSI
mkListEmpty pos = mkPrim pos ListEmpty

mkApp :: Pos -> ExpSI -> [ExpSI] -> ExpSI
mkApp pos f = foldl (\g -> withPos pos . EApp g) f

mkPrim :: Pos -> Prim -> ExpSI
mkPrim pos p = withPos pos $ EPrim p

withPos :: Pos -> ExpSITopLevel -> ExpSI
withPos pos esi = Fix $ InL (InL esi) :*: K pos

------------------------------------------------------------
-- Parsers for type annotations

pTypeAnn = pType'e >>= either (fail . render) return
  where
    pType'e = unboundTyVarCheck <$> getPosition <*> pType

pType = pTForAll
    <|> pTFun
    <|> pType'

pType' = pTVar
     <|> pTInt
     <|> pTDbl
     <|> pTBool
     <|> pTChar
     <|> pTBlob
     <|> pTText
     <|> pTRecord
     <|> pTVariant
     <|> pTList
     {- <|> pTMaybe -}
     <|> parens pType

pTForAll = pTForAll'e >>= either (fail . render) return
  where
    pTForAll'e = mkTForAll
        <$> getPosition
        <*> (reserved "forall" *> many1 pTyVar <* dot)
        <*> option [] (try pConstraints)
        <*> pType
        <?> "forall type annotation"

pConstraints = ((:[]) <$> pConstraint
           <|> parens (pConstraint `sepBy1` comma))
           <* reservedOp "=>"

pConstraint = pStarConstraint
          <|> pRowConstraint

pStarConstraint = (\c n -> (n, c))
              <$> (CStar <$> pStarHierarchy)
              <*> lowerIdentifier
  where
    pStarHierarchy = reserved "Eq"  *> pure CEq
                 <|> reserved "Ord" *> pure COrd
                 <|> reserved "Num" *> pure CNum

pRowConstraint = (,)
             <$> (lowerIdentifier <* reservedOp "\\")
             <*> (lacks . (:[]) <$> identifier)

-- simple syntactic check for unbound type variables in type annotations
unboundTyVarCheck :: Pos -> Type -> Either Doc Type
unboundTyVarCheck pos t
    | not (null freeVars) = Left $ vcat
          [ ppPos pos <> ":"
          , "unbound type variable(s)" <+> parensList (map ppTyVarName freeVars) <+> "in type annotation."
          ]
    | otherwise           = return t
  where
    freeVars    = S.toList $ S.delete "_" (S.map tyvarName $ ftv t)
    ppTyVarName = dquotes . text

-- match up constraints and bound type variables
mkTForAll :: Pos -> [TyVar] -> [(Name, Constraint)] -> Type -> Either Doc Type
mkTForAll pos tvs (M.fromListWith unionConstraints -> m) t
    | not (null badNames) = Left $ vcat
          [ ppPos pos <> ":"
          , "constraint(s) reference unknown type variable(s):" <+> parensList (map (dquotes . text) badNames)
          ]
    | otherwise = return $ withAnn pos (TForAllF tvs' t')
  where
    t' = substTyVar tvs (map (withAnn pos . TVarF) tvs') t
    tvs' = [ maybe tv (setConstraint tv) $ M.lookup (tyvarName tv) m
           | tv <- tvs
           ]
    setConstraint tv c = tv { tyvarConstraint = c }
    bndrs     = S.fromList $ map tyvarName tvs
    badNames  = S.toList $ M.keysSet m  S.\\ bndrs

pTVar = (\pos -> withAnn pos . TVarF)
    <$> getPosition
    <*> (pTyVar <|> pTWildcard)

pTInt  = pTCon TIntF "Int"
pTDbl  = pTCon TDblF "Double"
pTBool = pTCon TBoolF "Bool"
pTChar = pTCon TCharF "Char"
pTBlob = pTCon TBlobF "Blob"
pTText = pTCon TTextF "Text"

pTFun = (\pos a b -> withAnn pos (TFunF a b))
     <$> getPosition
     <*> try (pType' <* reservedOp "->" <* whiteSpace) -- TODO
     <*> pType
     <?> "function type annotation"

pTCon c s = (\pos -> withAnn pos c) <$> getPosition <* reserved s

pTyVar = mkTyVar Bound <$> lowerIdentifier
pTWildcard = mkTyVar Wildcard "_" <$ reservedOp "_"

mkTyVar flavour name = TyVar flavour name (head name) CNone

pTRecord = mkFromRowType TRecordF
       <$> getPosition
       <*> (try (Just <$> braces pTVar) <|> (braces $ optionMaybe (pTRowBody pTRecordEntry)))
       <?> "record type annotation"

pTVariant = mkFromRowType TVariantF
       <$> getPosition
       <*> (try (Just <$> angles pTVar) <|> (angles $ optionMaybe (pTRowBody pTVariantEntry)))
       <?> "variant type annotation"

pTRowBody pEntry = mkTRowExtend
               <$> getPosition
               <*> pEntry
               <*> pRest
  where
    pRest = (comma          *> pTRowBody pEntry)  <|>
            (reservedOp "|" *> pType')            <|>
            (mkTRowEmpty <$> getPosition)

mkFromRowType tCon pos =
    withAnn pos . tCon . fromMaybe (mkTRowEmpty pos)

pTRecordEntry = (,) <$> pRecordLabel <*> (reservedOp ":" *> pType)
pTVariantEntry = (,) <$> pVariantLabel <*> (reservedOp ":" *> pType)

mkTRowExtend pos (l, ty) r = withAnn pos $ TRowExtendF l ty r
mkTRowEmpty pos = withAnn pos TRowEmptyF

pTList = (\pos -> withAnn pos . TListF)
     <$> getPosition
     <*> brackets pType

{- pTMaybe = (\pos -> withAnn pos . TMaybeF) -}
     {- <$> getPosition -}
     {- <*> (reserved "Maybe" *> pType') -}

------------------------------------------------------------
-- Language definition for Lexer

languageDef :: P.LanguageDef st
languageDef = emptyDef
    { P.commentStart   = "{-"
    , P.commentEnd     = "-}"
    , P.commentLine    = "--"
    , P.nestedComments = True
    , P.identStart     = letter
    , P.identLetter    = alphaNum <|> oneOf "_'"
    , P.opStart        = P.opLetter languageDef
    , P.opLetter       = oneOf ":!#$%&*+./<=>?@\\^|-~"
    , P.reservedOpNames= [ "->", "=", "-", "*", "/", "+"
                         , "++", "::", "|", ",", ".", "\\"
                         , "{|", "|}", ":=", "{..}"
                         , "==", "/=", ">", ">=", "<", "<="
                         , "&&", "||", ":", "=>"
                         ]
    , P.reservedNames  = [ "let", "in", "if", "then", "else", "case", "of", "static"
                         , "True", "False", {-"Just", "Nothing",-} "forall"
                         , "Eq", "Ord", "Num"
                         ]
    , P.caseSensitive  = True
    }


------------------------------------------------------------
-- Lexer

lexer = P.makeTokenParser languageDef

lowerIdentifier = lookAhead lower >> identifier
upperIdentifier = lookAhead upper >> identifier

identifier = P.identifier lexer
reserved = P.reserved lexer
operator = P.operator lexer
reservedOp = P.reservedOp lexer
charLiteral = P.charLiteral lexer
stringLiteral = P.stringLiteral lexer
--natural = P.natural lexer
--integer = P.integer lexer
--float = P.float lexer
naturalOrFloat = P.naturalOrFloat lexer
--decimal = P.decimal lexer
--hexadecimal = P.hexadecimal lexer
--octal = P.octal lexer
symbol = P.symbol lexer
lexeme = P.lexeme lexer
whiteSpace = P.whiteSpace lexer
parens = P.parens lexer
braces = P.braces lexer
angles = P.angles lexer
brackets = P.brackets lexer
semi = P.semi lexer
comma = P.comma lexer
colon = P.colon lexer
dot = P.dot lexer
semiSep = P.semiSep lexer
semiSep1 = P.semiSep1 lexer
commaSep = P.commaSep lexer
commaSep1 = P.commaSep1 lexer
