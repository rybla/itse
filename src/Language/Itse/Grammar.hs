module Language.Itse.Grammar where

{-
## Prgm, Stmt
-}

data Prgm
  = Prgm [Stmt]
  deriving (Show, Eq)

data Stmt
  = Stmt_DefnTm (Name Term) Type Term
  | Stmt_DefnTy (Name Type) Kind Type
  | Stmt_DefnKd (Name Kind) Kind
  deriving (Show, Eq)

{-
## Term, Type, Kind
-}

data Term
  = -- x
    Term_Ref (Name Term)
  | -- λ x : t . a
    Term_AbsTm (Name Term) Type Term
  | -- a b
    Term_AppTm Term Term
  | -- λ x : k . a
    Term_AbsTy (Name Type) Kind Term
  | -- a t
    Term_AppTy Term Type
  deriving (Show, Eq)

data Type
  = -- x
    Type_Ref (Name Type)
  | -- λ x : s . t
    Type_AbsTm (Name Term) Type Type
  | -- t a
    Type_AppTm Type Term
  | -- λ x : k . t
    Type_AbsTy (Name Type) Kind Type
  | -- s t
    Type_AppTy Type Type
  | -- ι x . t
    Type_Iota (Name Term) Type
  deriving (Show, Eq)

data Kind
  = -- `*`
    Kind_Unit
  | -- Π x : t . k
    Kind_AbsTm (Name Term) Type Kind
  | -- Π x : k . t
    Kind_AbsTy (Name Type) Kind Kind
  deriving (Show, Eq)

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

class ToExpr a where
  toExpr :: a -> Expr a

instance ToExpr Term where toExpr = Term

instance ToExpr Type where toExpr = Type

instance ToExpr Kind where toExpr = Kind

instance Show (Expr a) where
  show (Term a) = show a
  show (Type t) = show t
  show (Kind k) = show k

{-
## Name
-}

data Name :: * -> * where
  NameTm :: String -> Name Term
  NameTy :: String -> Name Type
  NameKd :: String -> Name Kind

instance Show (Name a) where
  show (NameTm x) = x
  show (NameTy x) = x
  show (NameKd x) = x

instance Eq (Name a) where
  NameTm x == NameTm y = x == y
  NameTy x == NameTy y = x == y
  NameKd x == NameKd y = x == y

nameVariant :: Name a -> String
nameVariant (NameTm _) = "term"
nameVariant (NameTy _) = "type"
nameVariant (NameKd _) = "kind"
