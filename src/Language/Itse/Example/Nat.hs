module Language.Itse.Example.Nat where

-- import Control.Applicative
-- import Control.Monad.Except
-- import Data.Maybe
-- import Language.Itse.Checking
-- import Text.Printf
import Language.Itse.Grammar

-- Nat :: *
-- Nat := ι x . λ (P : Nat -> *) . λ (n : Nat . P n -> P (suc n)) -> P zero -> P x
itse_Nat :: Type
itse_Nat =
  (Type_Iota x) -- ι x .
    ( (Type_AbsTy p (Type_Ref nat `Kind_ArrTm` Kind_Unit)) -- λ p : Nat -> * .
        ( ( (Type_AbsTm n (Type_Ref nat)) -- λ n : Nat .
              ( (Type_AppTm (Type_Ref p) (Term_Ref n)) -- P n ->
                  `Type_ArrTm` (Type_AppTm (Type_Ref p) (Term_AppTm (Term_Ref suc) (Term_Ref n))) -- P (suc n)
              )
          )
            `Type_ArrTm` ( (Type_AppTm (Type_Ref p) (Term_Ref zero)) -- P zero ->
                             `Type_ArrTm` (Type_AppTm (Type_Ref p) (Term_Ref x)) -- P x
                         )
        )
    )
  where
    x = NameTm $ Literal "x"
    p = NameTy $ Literal "P"
    nat = NameTy $ Literal "Nat"
    n = NameTm $ Literal "n"
    suc = NameTm $ Literal "suc"
    zero = NameTm $ Literal "zero"

-- suc :: Nat -> Nat
-- suc := λ t : * . λ n : t . λ s : t . λ z . s n (n s z)
itse_suc :: Term
itse_suc = undefined

-- zero :: Nat
-- zero := λ t : * . λ s : t . λ z : t . z
itse_zero :: Term
itse_zero = undefined
