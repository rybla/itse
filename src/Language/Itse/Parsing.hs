{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC "-Wno-missing-signatures" #-}
{-# OPTIONS_GHC "-Wno-unused-do-bind" #-}

module Language.Itse.Parsing where

import Control.Monad
import Control.Monad.State
import Language.Itse.Grammar
import Text.Parsec hiding (State)
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token
import Text.Printf (printf)

type Parser a = Parsec String String a

{-
### Prgm and Stmt
-}

prgm :: Parser Prgm
prgm = Prgm <$> many stmt

stmt :: Parser Stmt
stmt =
  choice . map try $
    [ stmt_DefnTm,
      stmt_DefnTy
    ]

stmt_DefnTm, stmt_DefnTy :: Parser Stmt
stmt_DefnTm =
  Stmt_DefnTm
    <$> (symbol "define" >> symbol "term" >> nameTm)
    <*> (typingConstraint >> type_)
    <*> (assignment >> term)
stmt_DefnTy =
  Stmt_DefnTy
    <$> (symbol "define" >> symbol "type" >> nameTy)
    <*> (typingConstraint >> kind)
    <*> (assignment >> type_)

{-
### Term
-}

term, term1 :: Parser Term
term =
  (choice . map try)
    [ term_App,
      term1
    ]
term1 =
  (choice . map try)
    [ parens term,
      term_Abs,
      term_Ref
    ]

term_Ref, term_Abs, term_App :: Parser Term
term_Ref = Term_Ref <$> nameTm
term_Abs = do
  lambda
  foldl (\f p -> f . term_Abs' p)
    <$> (prm >>= pure . term_Abs')
    <*> many prm
    <*> term
  where
    term_Abs' = \case
      Left (x, t) -> Term_AbsTm x t
      Right (x, k) -> Term_AbsTy x k
term_App = do
  foldl term_App'
    <$> (do a <- term1; arg >>= pure . term_App' a)
    <*> many arg
  where
    term_App' a = \case
      Left b -> Term_AppTm a b
      Right t -> Term_AppTy a t

{-
### Type
-}

type_ :: Parser Type
type_ = buildExpressionParser table type1
  where
    table =
      [[binary "->" (Type_AbsTm $ toName "_") AssocRight]]
    binary name cons assoc = Infix (reservedOp name >> return cons) assoc

type1, type2, type3 :: Parser Type
type1 =
  choice . map try $
    [ type_Abs,
      type_Iota,
      type2
    ]
type2 =
  choice . map try $
    [ type_App,
      type3
    ]
type3 =
  choice . map try $
    [ parens type_,
      type_Ref
    ]

type_Ref, type_App, type_Abs, type_Iota :: Parser Type
type_Ref = Type_Ref <$> nameTy
type_Abs = do
  lambda
  foldl (\f p -> f . type_Abs' p)
    <$> (prm >>= pure . type_Abs')
    <*> many prm
    <*> type_
  where
    type_Abs' = \case
      Left (x, t) -> Type_AbsTm x t
      Right (x, k) -> Type_AbsTy x k
type_App = do
  foldl type_App'
    <$> (do a <- type3; arg >>= pure . type_App' a)
    <*> many arg
  where
    type_App' s = \case
      Left a -> Type_AppTm s a
      Right t -> Type_AppTy s t
type_Iota =
  do iota; x <- prmIota; t <- type_; return $ Type_Iota x t

{-
### Kind
-}

kind :: Parser Kind
kind = buildExpressionParser table kind1
  where
    table =
      [[binary "->" (Kind_AbsTy $ toName "_") AssocRight]]
    binary name cons assoc = Infix (reservedOp name >> return cons) assoc

kind1 :: Parser Kind
kind1 =
  choice . map try $
    [ kind_Unit,
      kind_AbsTm,
      kind_AbsTy
    ]

kind_Unit, kind_AbsTm, kind_AbsTy :: Parser Kind
kind_Unit = do point; return Kind_Unit
kind_AbsTm = do lambda; (x, t) <- prmTm; k <- kind; return $ Kind_AbsTm x t k
kind_AbsTy = do lambda; (x, k) <- prmTy; l <- kind; return $ Kind_AbsTy x k l

{-
### Name
-}

nameTm :: Parser (Name Term)
nameTm = NameTm <$> identifier

nameTy :: Parser (Name Type)
nameTy = NameTy <$> identifier

{-
### Utilities
-}

point, lambda, iota, par0, par1, brk0, brk1 :: Parser ()
point = void $ symbol "•"
lambda = void $ symbol "λ"
iota = void $ symbol "ι"
par0 = void $ symbol "("
par1 = void $ symbol ")"
brk0 = void $ symbol "{"
brk1 = void $ symbol "}"

wild :: ToName a => Parser (Name a)
wild = toName <$> symbol "_"

-- parameters
prmTm :: Parser (Name Term, Type)
prmTm = brackets do x <- (nameTm <|> wild); colon; t <- type_; return (x, t)

prmTy :: Parser (Name Type, Kind)
prmTy = braces do x <- (nameTy <|> wild); colon; k <- kind; return (x, k)

prmIota :: Parser (Name Term)
prmIota = brackets nameTm

prm :: Parser (Either (Name Term, Type) (Name Type, Kind))
prm = Left <$> prmTm <|> Right <$> prmTy

-- arguments
argTm :: Parser Term
argTm = brackets term

argTy :: Parser Type
argTy = braces type_

arg :: Parser (Either Term Type)
arg = Left <$> argTm <|> Right <$> argTy

typingBinding, typingConstraint, assignment :: Parser ()
typingBinding = void $ symbol ":"
typingConstraint = void $ symbol "::"
assignment = void $ symbol ":="

{-
## Language Def
-}

itseLanguageDef :: LanguageDef st
itseLanguageDef =
  emptyDef
    { Token.identStart = letter,
      Token.identLetter = alphaNum <|> oneOf "_'",
      Token.reservedOpNames = words "->",
      Token.caseSensitive = True
    }

itseTokenParser :: Token.TokenParser st
itseTokenParser = Token.makeTokenParser itseLanguageDef

identifier = Token.identifier itseTokenParser

symbol = Token.symbol itseTokenParser

parens = Token.parens itseTokenParser

brackets = Token.brackets itseTokenParser

braces = Token.braces itseTokenParser

colon = Token.colon itseTokenParser

reservedOp = Token.reservedOp itseTokenParser

{-
## Unique Wildcards

Each wildcard from "_" to a unique name of the form "_<int>". This will not
overlap with a legal identifier since '_' cannot be the start of an identifier.
-}

uniqueWildcards_Prgm :: Prgm -> Prgm
uniqueWildcards_Prgm = \case
  Prgm stmts -> Prgm (uniqueWildcards_Stmt <$> stmts)

uniqueWildcards_Stmt :: Stmt -> Stmt
uniqueWildcards_Stmt = \case
  Stmt_DefnTm x t a -> Stmt_DefnTm x (uniqueWildcards t) (uniqueWildcards a)
  Stmt_DefnTy x k t -> Stmt_DefnTy x (uniqueWildcards k) (uniqueWildcards t)

uniqueWildcards :: ToExpr a => a -> a
uniqueWildcards _e = evalState (go _e) 0
  where
    go :: ToExpr a => a -> State Int a
    go e = case toExpr e of
      Term _ -> case e of
        Term_Ref x ->
          return $ Term_Ref x
        Term_AbsTm x t a ->
          Term_AbsTm <$> procName x <*> go t <*> go a
        Term_AbsTy x k t ->
          Term_AbsTy <$> procName x <*> go k <*> go t
        Term_AppTm a b ->
          Term_AppTm <$> go a <*> go b
        Term_AppTy a t ->
          Term_AppTy <$> go a <*> go t
      Type _ -> case e of
        Type_Ref x ->
          return $ Type_Ref x
        Type_AbsTm x s t ->
          Type_AbsTm <$> procName x <*> go s <*> go t
        Type_AbsTy x k t ->
          Type_AbsTy <$> procName x <*> go k <*> go t
        Type_AppTm t a ->
          Type_AppTm <$> go t <*> go a
        Type_AppTy s t ->
          Type_AppTy <$> go s <*> go t
        Type_Iota x t ->
          Type_Iota <$> procName x <*> go t
      Kind _ ->
        return e

    procName :: ToName a => Name a -> State Int (Name a)
    procName x = if isWildcard x then uniqWild else return x

    uniqWild :: ToName a => State Int (Name a)
    uniqWild = do
      i <- get
      modify (+ 1)
      return . toName $ printf "_%i" i

isWildcard :: Name a -> Bool
isWildcard = ("_" ==) . fromName

{-
## Static Parsing
-}

runParserStatic :: ToExpr a => String -> Parser a -> String -> a
runParserStatic lbl prs src = case runParser (do a <- prs; eof; return a) "" lbl src of
  Left expt -> error . show $ expt
  Right a -> uniqueWildcards a
