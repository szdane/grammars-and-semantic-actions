open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Syntax (Σ₀ : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List as List
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' : Level

data Pos : Type (ℓ-suc ℓ-zero)
data Neg : Type (ℓ-suc ℓ-zero)

data Pos where
  lit : ⟨ Σ₀ ⟩ → Pos -- arbitrary?
  ε : Pos
  _⊗_ : Pos → Pos → Pos
  ⊕ : ∀ {X : Type} → (X → Pos) → Pos
  ↓ : Neg → Pos
data Neg where
  _⊸_ : Pos → Neg → Neg
  & : ∀ {X : Type} → (X → Neg) → Neg
  ↑ : Pos → Neg

Ctx : Type (ℓ-suc ℓ-zero)
Ctx = List Pos

data Val : Ctx → Pos → Type (ℓ-suc ℓ-zero)
data Comp : Ctx → Neg → Type (ℓ-suc ℓ-zero)
leftover : ∀ {Γ A} → Val Γ A → Ctx

data Val where
  var : ∀ {Γ}{A} → Val (A ∷ Γ) A
  ⟨⟩ : ∀ {Γ} → Val Γ ε
  ⟨_,_⟩ : ∀ {Γ A A'} → (V : Val Γ A) → (V' : Val (leftover V) A') → Val Γ (A ⊗ A')
  ⊕inj : ∀ {Γ X A} (x : X) → Val Γ (A x) → Val Γ (⊕ A)
  ↓ : ∀ {Γ B} → (M : Comp Γ B) → Val Γ (↓ B)

leftover (var {Γ = Γ}) = Γ
leftover (⟨⟩ {Γ = Γ}) = Γ
leftover (⊕inj x V) = leftover V
leftover (⟨ V , V' ⟩) = leftover V'
leftover (↓ M) = []

data Comp where
  app : ∀ {Γ A B} → (V : Val Γ A) → (M : Comp (leftover V) (A ⊸ B)) → Comp Γ B
  λ⊸ :  ∀ {Γ A B} → Comp (A ∷ Γ) B → Comp Γ (A ⊸ B)
  ⊗-elim : ∀ {Γ A A' B} → Comp (A ∷ A' ∷ Γ) B → Comp ((A ⊗ A') ∷ Γ) B
  ε-elim : ∀ {Γ B} → Comp Γ B → Comp (ε ∷ Γ) B
  ⊕-elim : ∀ {Γ X A B} → (∀ (x : X) → Comp (A x ∷ Γ) B) → Comp ((⊕ A) ∷ Γ) B
  &π : ∀ {Γ X B} → (x : X) → Comp Γ (& B) → Comp Γ (B x)
  λ& : ∀ {Γ X B} → ((x : X) → Comp Γ (B x)) → Comp Γ (& B)
  ↓e : ∀ {Γ B} → (V : Val Γ (↓ B)) → leftover V ≡ [] → Comp Γ B
  ↑ : ∀ {Γ A} → (V : Val Γ A) → leftover V ≡ [] → Comp Γ (↑ A)
  ↑e : ∀ {Γ Γ' A B} → (M : Comp Γ (↑ A)) (N : Comp (A ∷ Γ') B) → Comp (Γ ++ Γ') B
-- data _⊢_ {ℓ} : Ctx ℓ → Lin ℓ → Type (ℓ-suc ℓ)
-- leftover : ∀ {Γ : Ctx ℓ}{A : Lin ℓ} → Γ ⊢ A → Ctx ℓ

-- data _⊢_ where
--   var : ∀ {Γ}{A} → (A ∷ Γ) ⊢ A
--   ⟨⟩ : ∀ {Γ} → Γ ⊢ ε
--   ⟨_,_⟩ : ∀ {Γ A A'} → (M : Γ ⊢ A) (N : leftover M ⊢ A') → Γ ⊢ (A ⊗ A')
--   ⟜app :  ∀ {Γ A A'} →  (M : Γ ⊢ (A' ⟜ A)) (N : leftover M ⊢ A) → Γ ⊢ A'
--   λ⟜ : ∀ {Γ A B} → (M : (A ∷ Γ) ⊢ B) → Γ ⊢ (B ⟜ A)

-- leftover (var {Γ = Γ}) = Γ
-- leftover (⟨⟩ {Γ = Γ}) = Γ
-- leftover (⟨ M , N ⟩) = leftover N
-- leftover (⟜app M N) = leftover N
-- leftover (λ⟜


-- -- a closed term is one that uses all of the variables that are in scope
-- ↓ : Lin ℓ → Type (ℓ-suc ℓ)
-- ↓ {ℓ = ℓ} A =
--   Σ[ M ∈ ([] ⊢ A) ] leftover M ≡ []
