module Language.Itse.Example.Nat where

-- import Control.Applicative
-- import Control.Monad.Except
-- import Data.Maybe
-- import Language.Itse.Checking
-- import Text.Printf
import Language.Itse.Grammar
import Language.Itse.Parsing

{-
Nat
:: •
:= ι[x]
   λ{P : λ[_:Nat] •}
   (λ[n : Nat] (P[n] -> P[suc[n]]) ->
      P[zero] ->
      P[x])

suc
:: Nat -> Nat
:= λ{A : •} λ[n : Nat] [s : A -> A] λ[z : A] s[n][n[s][z]]

zero
:: Nat
:= λ{A : •} [s : A -> A] [z : A] z
-}

itse_Nat :: Type
itse_Nat =
  runParserStatic "Nat" type_ $
    "ι[x] λ{P : λ[_:Nat] •} (λ[n : Nat] (P[n] -> P[suc[n]]) -> P[zero] -> P[x])"

itse_suc :: Term
itse_suc =
  runParserStatic "suc" term $
    "λ {A : •} [n : Nat] [s : A -> A] [z : A] s[n][n[s][z]]"

itse_zero :: Term
itse_zero =
  runParserStatic "zero" term $
    "λ {A : •} [s : A -> A] [z : A] z"
