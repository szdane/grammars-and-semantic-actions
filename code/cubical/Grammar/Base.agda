{-# OPTIONS --erased-cubical --erasure #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Base
  (Alphabet : Type ℓ-zero)
  (isSetAlphabet : isSet Alphabet)
  where

open import String.Base Alphabet isSetAlphabet
open import String.Splitting Alphabet isSetAlphabet

private
  variable ℓA : Level

module _ where
  module _ ℓA where
    Grammar : Type (ℓ-suc ℓA)
    Grammar = String → Type ℓA
