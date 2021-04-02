{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC "-Wno-missing-signatures" #-}
{-# OPTIONS_GHC "-Wno-unused-do-bind" #-}

module Language.Itse.Parsing where

import Control.Monad
import Language.Itse.Grammar
import Text.Parsec
import Text.Parsec.Language
import qualified Text.Parsec.Token as Token

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

term, term' :: Parser Term
term =
  (choice . map try)
    [ term_App,
      term'
    ]
term' =
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
    <$> (do a <- term'; arg >>= pure . term_App' a)
    <*> many arg
  where
    term_App' a = \case
      Left b -> Term_AppTm a b
      Right t -> Term_AppTy a t

{-
### Type
-}

type_, type' :: Parser Type
type_ =
  choice . map try $
    [ type_App,
      type'
    ]
type' =
  choice . map try $
    [ parens type_,
      type_Abs,
      type_Iota,
      type_Ref
    ]

type_Ref, type_App, type_Abs, type_Iota :: Parser Type
type_Ref = Type_Ref <$> nameTy
type_Abs = do
  lambda
  foldl (\f p -> f . type_Abs' p)
    <$> (prm >>= pure . type_Abs')
    <*> many prm
    <*> type'
  where
    type_Abs' = \case
      Left (x, t) -> Type_AbsTm x t
      Right (x, k) -> Type_AbsTy x k
type_App = do
  foldl type_App'
    <$> (do a <- type'; arg >>= pure . type_App' a)
    <*> many arg
  where
    type_App' s = \case
      Left a -> Type_AppTm s a
      Right t -> Type_AppTy s t
type_Iota = do iota; x <- parens nameTm; t <- type_; return $ Type_Iota x t

{-
### Kind
-}

kind :: Parser Kind
kind =
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

nameKd :: Parser (Name Kind)
nameKd = NameKd <$> identifier

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

wild :: Parser String
wild = symbol "_"

-- parameters
prmTm :: Parser (Name Term, Type)
prmTm = parens do x <- (nameTm <|> NameTm <$> symbol "_"); colon; t <- type_; return (x, t)

prmTy :: Parser (Name Type, Kind)
prmTy = braces do x <- (nameTy <|> NameTy <$> symbol "_"); colon; k <- kind; return (x, k)

prm :: Parser (Either (Name Term, Type) (Name Type, Kind))
prm = Left <$> prmTm <|> Right <$> prmTy

-- arguments
argTm :: Parser Term
argTm = parens term

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

test p s = runParser (do a <- p; eof; return a) "" "" s
