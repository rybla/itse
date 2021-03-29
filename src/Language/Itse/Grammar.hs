module Language.Itse.Grammar where

data Term
  = -- x
    Term_Ref (Name Term)
  | -- λ x : t . a
    Term_Abs (Name Term) Type Term
  | -- a b
    Term_App Term Term
  deriving (Show, Eq)

data Type
  = -- x
    Type_Ref (Name Type)
  | -- forall x : k . t
    Type_All (Name Type) Kind Type
  | -- Π x : s . t
    Type_Pi (Name Term) Type Type
  | -- forall x : s . t
    Type_AllDep (Name Term) Type Type
  | -- ι x . t
    Type_Iota (Name Term) Type
  | -- t a
    Type_AppDep Type Term
  | -- λ x : k . t
    Type_Abs (Name Type) Kind Type
  | -- λ x : s . t
    Type_AbsDep (Name Term) Type Type
  | -- s t
    Type_App Type Type
  deriving (Show, Eq)

data Kind
  = -- `*`
    Kind_Unit
  | -- Π x : t . k
    Kind_PiDep (Name Term) Type Kind
  | -- Π x : k . t
    Kind_Pi (Name Type) Kind Kind
  deriving (Show, Eq)

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

data Name :: * -> * where
  NameTerm :: String -> Name Term
  NameType :: String -> Name Type
  NameKind :: String -> Name Kind

instance Show (Name a) where
  show (NameTerm x) = x
  show (NameType x) = x
  show (NameKind x) = x

instance Eq (Name a) where
  NameTerm x == NameTerm y = x == y
  NameType x == NameType y = x == y
  NameKind x == NameKind y = x == y

nameVariant :: Name a -> String
nameVariant (NameTerm _) = "term"
nameVariant (NameType _) = "type"
nameVariant (NameKind _) = "kind"
