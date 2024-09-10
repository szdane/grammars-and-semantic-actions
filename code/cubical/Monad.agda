open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Monad (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Term Alphabet

private
  variable
    ℓg ℓh ℓk : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk

-- TODO change the levels to not be fixed
record Monad
  {ℓ-map : Level → Level}
  (M : ∀ {ℓg} → Grammar ℓg → Grammar (ℓ-map ℓg))
    : Typeω where
  field
    return : ∀ {g : Grammar ℓg} → g ⊢ M g
    μ : ∀ {g : Grammar ℓg} → M (M g) ⊢ M g
    fmap : ∀ {g : Grammar ℓg}{h : Grammar ℓh} → g ⊢ h → M g ⊢ M h

record LeftStrongMonad
  {ℓ-map : Level → Level}
  (M : ∀ {ℓg} → Grammar ℓg → Grammar (ℓ-map ℓg))
    : Typeω where
  field
    monad : Monad M
    leftStrength : ∀ {g : Grammar ℓg}{h : Grammar ℓh} →
      g ⊗ M h ⊢ M (g ⊗ h)

record RightStrongMonad
  {ℓ-map : Level → Level}
  (M : ∀ {ℓg} → Grammar ℓg → Grammar (ℓ-map ℓg))
    : Typeω where
  field
    monad : Monad M
    rightStrength : ∀ {g : Grammar ℓg}{h : Grammar ℓh} →
      M g ⊗ h ⊢ M (g ⊗ h)

record StrongMonad
  {ℓ-map : Level → Level}
  (M : ∀ {ℓg} → Grammar ℓg → Grammar (ℓ-map ℓg))
    : Typeω where
  field
    monad : Monad M
    leftStrength : ∀ {g : Grammar ℓg}{h : Grammar ℓh} →
      g ⊗ M h ⊢ M (g ⊗ h)
    rightStrength : ∀ {g : Grammar ℓg}{h : Grammar ℓh} →
      M g ⊗ h ⊢ M (g ⊗ h)
