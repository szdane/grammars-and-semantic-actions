open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Exception (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Term Alphabet
open import Monad Alphabet

private
  variable
    ℓg ℓh ℓk : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk

module _ (h : Grammar ℓh) where
  Exception : Grammar ℓg → Grammar (ℓ-max ℓg ℓh)
  Exception g = g ⊕ h

  throw : h ⊢ Exception g
  throw = ⊕-inr

  open Monad
  open StrongMonad

  ExceptionMonad : Monad Exception
  ExceptionMonad .return = ⊕-inl
  ExceptionMonad .μ =
    ⊕-elim id throw
  ExceptionMonad .fmap e = ⊕-elim (⊕-inl ∘g e) throw

