{-# LANGUAGE PatternSynonyms #-}

module Language.Itse.Grammar where

-- import qualified Text.Pretty as Py
-- import Text.Printf (printf)

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
  | -- λ (x : t) a
    Term_AbsTm (Name Term) Type Term
  | -- a (b)
    Term_AppTm Term Term
  | -- λ {x : k} . a
    Term_AbsTy (Name Type) Kind Term
  | -- a {t}
    Term_AppTy Term Type
  deriving (Show, Eq)

data Type
  = -- x
    Type_Ref (Name Type)
  | -- λ (x : s) t
    Type_AbsTm (Name Term) Type Type
  | -- t (a)
    Type_AppTm Type Term
  | -- λ {x : k} t
    Type_AbsTy (Name Type) Kind Type
  | -- s {t}
    Type_AppTy Type Type
  | -- ι (x) t
    Type_Iota (Name Term) Type
  deriving (Show, Eq)

-- pattern Type_ArrTm :: Type -> Type -> Type
-- pattern Type_ArrTm s t = Type_AbsTm (NameTm "_") s t

-- pattern Type_ArrTy :: Kind -> Type -> Type
-- pattern Type_ArrTy k t = Type_AbsTy (NameTy "_") k t

data Kind
  = -- `*`
    Kind_Unit
  | -- λ (x : t) k
    Kind_AbsTm (Name Term) Type Kind
  | -- λ {x : k} l
    Kind_AbsTy (Name Type) Kind Kind
  deriving (Show, Eq)

-- pattern Kind_ArrTm :: Type -> Kind -> Kind
-- pattern Kind_ArrTm t k = Kind_AbsTm Wild t k

-- pattern Kind_ArrTy :: Kind -> Kind -> Kind
-- pattern Kind_ArrTy k l = Kind_AbsTy Wild k l

{-
## Expr
-}

data Expr :: * -> * where
  Term :: Term -> Expr Term
  Type :: Type -> Expr Type
  Kind :: Kind -> Expr Kind

fromExpr :: Expr a -> a
fromExpr (Term a) = a
fromExpr (Type t) = t
fromExpr (Kind k) = k

-- class ToExpr a where
--   toExpr :: a -> Expr a

-- instance ToExpr Term where toExpr = Term

-- instance ToExpr Type where toExpr = Type

-- instance ToExpr Kind where toExpr = Kind

instance Show (Expr a) where
  show (Term a) = show a
  show (Type t) = show t
  show (Kind k) = show k

{-
## Param
-}

data Param a
  = Named (Name a)
  | Wild
  deriving (Eq, Show)

{-
## Name
-}

data Name :: * -> * where
  NameTm :: String -> Name Term
  NameTy :: String -> Name Type
  NameKd :: String -> Name Kind

instance Show (Name a) where
  show (NameTm x) = show x
  show (NameTy x) = show x
  show (NameKd x) = show x

instance Eq (Name a) where
  NameTm x == NameTm y = x == y
  NameTy x == NameTy y = x == y
  NameKd x == NameKd y = x == y

nameVariant :: Name a -> String
nameVariant (NameTm _) = "term"
nameVariant (NameTy _) = "type"
nameVariant (NameKd _) = "kind"

{-
## Pretty instances
-}

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
