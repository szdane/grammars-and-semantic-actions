open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Base (Alphabet : hSet ℓ-zero) where

open import String.Base Alphabet public
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓA ℓX : Level
    X : Type ℓX

module _ where
  module _ ℓA where
    Grammar : Type (ℓ-suc ℓA)
    Grammar = String → Type ℓA

LevelOfG : Grammar ℓA → Level
LevelOfG {ℓA = ℓA} A = ℓA

LevelOfDepG : (X → Grammar ℓA) → Level
LevelOfDepG {ℓA = ℓA} A = ℓA
