open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Helper
open import Grammar.Base Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet
open import Term.Bilinear Alphabet

private
  variable
    ℓG ℓH ℓK : Level
    g : Grammar ℓG
    h : Grammar ℓH

opaque
  ε : Grammar ℓ-zero
  ε w = w ≡ []

