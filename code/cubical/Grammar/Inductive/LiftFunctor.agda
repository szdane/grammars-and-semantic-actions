{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Prelude.More
open import Cubical.Foundations.HLevels

module Grammar.Inductive.LiftFunctor (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Helper
open import Grammar.Base Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term.Base Alphabet

private
  variable ℓA ℓB ℓX ℓY ℓ : Level

module _ (X : Type ℓX) {ℓ'} where
  LiftFunctor : (F : Functor X ℓ) → Functor X (ℓ-max ℓ (ℓ-max ℓX ℓ'))
  LiftFunctor (k A) = k (LiftG (ℓ-max ℓX ℓ') A)
  LiftFunctor {ℓ = ℓ} (Var x) = Var {ℓ = ℓ-max ℓ ℓ'} x
  LiftFunctor (&e Y F) = &e Y (λ y → LiftFunctor (F y))
  LiftFunctor (⊕e Y F) = ⊕e Y (λ y → LiftFunctor (F y))
  LiftFunctor (⊗e F F₁) = ⊗e (LiftFunctor F) (LiftFunctor F₁)

  lowerFunctor :
    (F : Functor X ℓ) → {A : X → Grammar ℓA}
    → ⟦ LiftFunctor F ⟧ A ⊢ ⟦ F ⟧ A
  lowerFunctor (k A) = liftG ∘g lowerG ∘g lowerG
  lowerFunctor (Var x) = liftG ∘g lowerG
  lowerFunctor (&e Y F) = map&ᴰ (λ y → lowerFunctor (F y))
  lowerFunctor (⊕e Y F) = map⊕ᴰ (λ y → lowerFunctor (F y))
  lowerFunctor (⊗e F F₁) = lowerFunctor F ,⊗ lowerFunctor F₁

  liftFunctor :
    (F : Functor X ℓ) → {A : X → Grammar ℓA}
    → ⟦ F ⟧ A ⊢ ⟦ LiftFunctor F ⟧ A
  liftFunctor (k A) = liftG ∘g liftG ∘g lowerG
  liftFunctor (Var x) = liftG ∘g lowerG
  liftFunctor (&e Y F) = map&ᴰ (λ y → liftFunctor (F y))
  liftFunctor (⊕e Y F) = map⊕ᴰ (λ y → liftFunctor (F y))
  liftFunctor (⊗e F F₁) = liftFunctor F ,⊗ liftFunctor F₁

  open StrongEquivalence
  liftFunctor≅ :
    (F : Functor X ℓ) → {A : X → Grammar ℓA} →
    ⟦ LiftFunctor F ⟧ A ≅ ⟦ F ⟧ A

  liftFunctor≅ F .fun = lowerFunctor F
  liftFunctor≅ F .inv = liftFunctor F
  liftFunctor≅ (k A) .sec = refl
  liftFunctor≅ (Var x) .sec = refl
  liftFunctor≅ (&e Y F) .sec = &ᴰ≡ _ _ λ y → λ i → liftFunctor≅ (F y) .sec i ∘g &ᴰ-π y
  liftFunctor≅ (⊕e Y F) .sec = ⊕ᴰ≡ _ _ λ y → λ i → ⊕ᴰ-in y ∘g liftFunctor≅ (F y) .sec i
  liftFunctor≅ (⊗e F F₁) {A = A} .sec = ans
    where
      opaque
        unfolding ⊗-intro
        ans : lowerFunctor F {A = A} ,⊗ lowerFunctor F₁ {A = A}
              ∘g liftFunctor F ,⊗ liftFunctor F₁ ≡ id
        ans i = liftFunctor≅ F .sec i ,⊗ liftFunctor≅  F₁ .sec i
  liftFunctor≅ (k A) .ret = refl
  liftFunctor≅ (Var x) .ret = refl
  liftFunctor≅ (&e Y F) .ret = &ᴰ≡ _ _ λ y → λ i → liftFunctor≅ (F y) .ret i ∘g &ᴰ-π y
  liftFunctor≅ (⊕e Y F) .ret = ⊕ᴰ≡ _ _ λ y → λ i → ⊕ᴰ-in y ∘g liftFunctor≅ (F y) .ret i
  liftFunctor≅ (⊗e F F₁) {A = A} .ret = ans
    where
      opaque
        unfolding ⊗-intro
        ans : liftFunctor F {A = A} ,⊗ liftFunctor F₁ {A = A}
              ∘g lowerFunctor F ,⊗ lowerFunctor F₁ ≡ id
        ans i = liftFunctor≅ F .ret i ,⊗ liftFunctor≅  F₁ .ret i

