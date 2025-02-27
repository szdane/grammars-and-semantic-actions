open import Cubical.Foundations.Prelude
module Cubical.Foundations.Prelude.More where

private
  variable
    ℓ : Level

LevelOf : Type ℓ → Level
LevelOf {ℓ = ℓ} A = ℓ
