{-# LANGUAGE PatternSynonyms #-}

module Language.Itse.Grammar where

-- import qualified Text.Pretty as Py
import Text.Printf (printf)

{-
## Prgm, Stmt
-}

data Prgm
  = Prgm [Stmt]
  deriving (Show, Eq)

data Stmt
  = -- define term <name> :: <type> := <term>
    Stmt_DefnTm (Name Term) Type Term
  | -- define type <name> :: <kind> := <type>
    Stmt_DefnTy (Name Type) Kind Type
  deriving (Show, Eq)

{-
## Term, Type, Kind
-}

data Term
  = -- x
    Term_Ref (Name Term)
  | -- λ[x : t] a
    Term_AbsTm (Name Term) Type Term
  | -- a [b]
    Term_AppTm Term Term
  | -- λ{x : k} . a
    Term_AbsTy (Name Type) Kind Term
  | -- a {t}
    Term_AppTy Term Type
  deriving (Eq)

data Type
  = -- x
    Type_Ref (Name Type)
  | -- λ[x : s] t
    Type_AbsTm (Name Term) Type Type
  | -- t [a]
    Type_AppTm Type Term
  | -- λ{x : k} t
    Type_AbsTy (Name Type) Kind Type
  | -- s {t}
    Type_AppTy Type Type
  | -- ι [x] t
    Type_Iota (Name Term) Type
  deriving (Eq)

data Kind
  = -- `•`
    Kind_Unit
  | -- λ[x : t] k
    Kind_AbsTm (Name Term) Type Kind
  | -- λ{x : k} l
    Kind_AbsTy (Name Type) Kind Kind
  deriving (Eq)

{-
## Expr
-}

data Expr :: * -> * where
  Term :: Term -> Expr Term
  Type :: Type -> Expr Type
  Kind :: Kind -> Expr Kind

fromExpr :: Expr a -> a
fromExpr = \case
  Term a -> a
  Type t -> t
  Kind k -> k

class ToExpr a where
  toExpr :: a -> Expr a

instance ToExpr Term where toExpr = Term

instance ToExpr Type where toExpr = Type

instance ToExpr Kind where toExpr = Kind

asExpr :: ToExpr a => (Expr a -> Expr b) -> (a -> b)
asExpr f = fromExpr . f . toExpr

asExpr2 :: (ToExpr a, ToExpr b) => (Expr a -> Expr b -> Expr c) -> (a -> b -> c)
asExpr2 f e1 e2 = fromExpr $ f (toExpr e1) (toExpr e2)

asExprF :: (ToExpr a, Functor f) => (Expr a -> f (Expr a)) -> (a -> f a)
asExprF k = fmap fromExpr . k . toExpr

instance Show (Expr a) where
  show = \case
    Term a -> show a
    Type t -> show t
    Kind k -> show k

exprVariant :: Expr a -> String
exprVariant = \case
  Term _ -> "term"
  Type _ -> "type"
  Kind _ -> "kind"

{-
## Name
-}

data Name :: * -> * where
  NameTm :: String -> Name Term
  NameTy :: String -> Name Type
  NameKd :: String -> Name Kind

instance Show (Name a) where
  show = fromName

instance Eq (Name a) where
  NameTm x == NameTm y = x == y
  NameTy x == NameTy y = x == y
  NameKd x == NameKd y = x == y

fromName :: Name a -> String
fromName = \case
  NameTm x -> x
  NameTy x -> x
  NameKd x -> x

nameVariant :: Name a -> String
nameVariant = \case
  NameTm _ -> "term"
  NameTy _ -> "type"
  NameKd _ -> "kind "

class ToName a where
  toName :: String -> Name a

instance ToName Term where toName = NameTm

instance ToName Type where toName = NameTy

instance ToName Kind where toName = NameKd

{-
## Pretty instances
-}

instance Show Term where
  show = \case
    -- x
    Term_Ref x -> show x
    -- λ[x : t] a
    Term_AbsTm x t a -> printf "λ[%s : %s] %s" (show x) (show t) (show a)
    -- a[b]
    Term_AppTm a b -> printf "%s[%s]" (show a) (show b)
    -- λ{x : k} a
    Term_AbsTy x k a -> printf "λ{%s : %s} %s" (show x) (show k) (show a)
    -- a {t}
    Term_AppTy a t -> printf "%s{%s}" (show a) (show t)

instance Show Type where
  show = \case
    -- x
    Type_Ref x -> show x
    -- λ[x : s] t
    Type_AbsTm x s t -> printf "λ[%s : %s] %s" (show x) (show s) (show t)
    -- t [a]
    Type_AppTm t a -> printf "%s[%s]" (show t) (show a)
    -- λ{x : k} t
    Type_AbsTy x k t -> printf "λ{%s : %s} %s" (show x) (show k) (show t)
    -- s{t}
    Type_AppTy s t -> printf "%s{%s}" (show s) (show t)
    -- ι [x] t
    Type_Iota x t -> printf "ι[%s] %s" (show x) (show t)

instance Show Kind where
  show = \case
    -- `•`
    Kind_Unit -> "•"
    -- λ[x : t] k
    Kind_AbsTm x t k -> printf "λ[%s : %s] %s" (show x) (show t) (show k)
    -- λ{x : k} l
    Kind_AbsTy x k l -> printf "λ{%s : %s} %s" (show x) (show k) (show l)

-- instance Py.Pretty Term where
--   pretty = \case
--     Term_Ref x -> Py.Leaf (show x)
--     Term_AbsTm x t a ->
--       case a of
--         Term_AbsTm _ _ _ ->
--           (Py.Leaf $ printf "λ (%s : %s)" (show x) (show t)) <> Py.pretty a
--         Term_AbsTy _ _ _ ->
--           (Py.Leaf $ printf "λ (%s : %s)" (show x) (show t)) <> Py.pretty a
--         _ ->
--           Py.Branch
--             [ Py.Leaf $ printf "λ (%s : %s)" (show x) (show t),
--               Py.Branch
--                 [Py.Leaf $ show a]
--             ]
--     Term_AbsTy x k a ->
--       case a of
--         Term_AbsTm _ _ _ ->
--           (Py.Leaf $ printf "λ (%s : %s)" (show x) (show k)) <> Py.pretty a
--         Term_AbsTy _ _ _ ->
--           (Py.Leaf $ printf "λ (%s : %s)" (show x) (show k)) <> Py.pretty a
--         _ ->
--           Py.Branch
--             [ Py.Leaf $ printf "λ (%s : %s)" (show x) (show k),
--               Py.Branch
--                 [Py.Leaf $ show a]
--             ]
--     Term_AppTm a b -> Py.pretty a <> Py.pretty

-- instance Py.Pretty Type where
--   pretty = undefined

-- instance Py.Pretty Kind where
--   pretty = undefined
