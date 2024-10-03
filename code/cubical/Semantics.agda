{- This file records how each term construct of our type theory can be interpreted using our shallow embedding -}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Term Alphabet

private
  variable
    ℓG ℓG' ℓ ℓ' : Level
    Δ Δ' Δ₁ Δ₂ A A' B B' : Grammar ℓG
    X X' Y Y' Z Z' : Type ℓ

{- We interpret non-linear types as Types -}
{- We interpret linear contexts Δ and types A both as grammars -}

{- We typically do not need an ambient non-linear contexts as they are
modeled by Agda's ambient variables/weakening When we extend a
context, we model this using Agda function types -}

{- We interpret the empty context as ε and a concatenation as Δ ⊗ Δ' -}
{- We interpret a term Δ ⊢ M : A as a term M : Δ ⊢ A -}

⊗-intro'' : Δ ⊢ A → Δ' ⊢ A' → Δ ⊗ Δ' ⊢ A ⊗ A'
⊗-intro'' = _,⊗_

⊗-elim' :
  Δ ⊗ (A ⊗ A') ⊗ Δ' ⊢ B
  → Δ ⊗ A ⊗ A' ⊗ Δ' ⊢ B
⊗-elim' f = f ∘g id ,⊗ ⊗-assoc

-- TODO: ⊗-βη

⊕ᴰ-intro' :
  ∀ {A : X → Grammar ℓG} x →
  (Δ ⊢ A x) → Δ ⊢ LinΣ[ x ∈ X ] A x
⊕ᴰ-intro' x f = LinΣ-intro x ∘g f

⊕ᴰ-elim' :
  ∀ {A : X → Grammar ℓG}
  → (∀ x → (Δ ⊗ (A x) ⊗ Δ' ⊢ B))
  → Δ ⊗ (LinΣ[ x ∈ X ] A x) ⊗ Δ' ⊢ B
⊕ᴰ-elim' f = ⊸-intro⁻ (⟜-intro⁻ (LinΣ-elim (λ x →
  ⟜-intro (⊸-intro (f x)))))

-- TODO: ⊕ᴰ βη

&ᴰ-intro :
  ∀ {A : X → Grammar ℓG}
  → (∀ x → Δ ⊢ A x)
  → (Δ ⊢ &[ x ∈ X ] A x)
&ᴰ-intro = LinΠ-intro
    
&ᴰ-elim :
  ∀ {A : X → Grammar ℓG} x
  → (Δ ⊢ &[ x ∈ X ] A x)
  → (Δ ⊢ A x)
&ᴰ-elim x f = LinΠ-app x ∘g f

-- TODO: βη

I-intro : ε ⊢ ε
I-intro = id

I-elim : Δ ⊗ Δ' ⊢ A → Δ ⊗ ε ⊗ Δ' ⊢ A
I-elim f = f ∘g id ,⊗ ⊗-unit-l

-- ⊸-intro and ⟜-intro directly model the intro rules
⊸-elim :
  (Δ ⊢ A)
  → (Δ' ⊢ A ⊸ B)
  → (Δ ⊗ Δ' ⊢ B)
⊸-elim a f = ⊸-app ∘g a ,⊗ f

-- todo: βη

⟜-elim :
  (Δ ⊢ B ⟜ A)
  → (Δ' ⊢ A)
  → (Δ ⊗ Δ' ⊢ B)
⟜-elim f a = ⟜-app ∘g f ,⊗ a

-- aka "roll"
μ-intro :
  ∀ {A : X → Functor X}
    x
  → Δ ⊢ ⟦ A x ⟧ (μ A)
  → Δ ⊢ μ A x
μ-intro x f = roll ∘g f

-- the "basic elim"
μ-elim :
  ∀ {A : X → Functor X}{B : X → Grammar _}
  → (∀ x → ⟦ A x ⟧ B ⊢ B x)
  → ∀ x
  → Δ ⊢ μ A x
  → Δ ⊢ B x
μ-elim {A = A} f x e = rec A f x ∘g e

μ-β : ∀ {A : X → Functor X}{B : X → Grammar _}
      x
    → (e : Δ ⊢ ⟦ A x ⟧ (μ A))
    → (f : ∀ x → ⟦ A x ⟧ B ⊢ B x)
    → μ-elim {A = A}{B = B} f x (μ-intro x e) ≡
      f x ∘g map (A x) {!!} ∘g e -- f x ∘g map (A x) (λ a → μ-elim {A = A} {B = B} f a id) ∘g e
μ-β {A = A} x e f = cong (_∘g e) (rec-β A f x)

μ-η'' : ∀ {A : X → Functor X}{B : X → Grammar _}
  → (f : ∀ x → ⟦ A x ⟧ B ⊢ B x)
  → (e' : ∀ x → μ A x ⊢ B x)
  → (∀ x → e' x ∘g roll ≡ f x ∘g map (A x) e')
  → ∀ M
  → (e : Δ ⊢ μ A M)
  → μ-elim {A = A}{B = B} f M e ≡ e' M ∘g e
μ-η'' {A = A} f e' p M e = cong (_∘g e) (funExt⁻ (sym (μ-η A f (e' , p))) M)

-- higher order version of fold
μ-fold :
  ε ⊢ &[ X ∈ Type ℓ ]
      &[ A ∈ (X → Functor X) ]
      &[ B ∈ (X → Grammar _ ) ]
      &[ _ ∈ (ε ⊢ &[ x ∈ _ ] (⟦ A x ⟧ B ⊸ B x)) ]
      &[ x ∈ X ]
      (μ A x ⊸ B x)
μ-fold = LinΠ-intro (λ X → LinΠ-intro λ A → LinΠ-intro λ B → LinΠ-intro λ f → LinΠ-intro λ x → ⊸-intro (μ-elim {A = A} {B = B}(λ x → ⊸-app ∘g ⊸0⊗ (LinΠ-app x ∘g f)) x ⊗-unit-r))
-- μ-elimP :
--   ∀ {Δ₁}{Δ₂}{A : X → Functor X}{B : X → Grammar _}
--     {x}
--   → (∀ x → Δ₁ ⊗ ⟦ A x ⟧ B ⊗ Δ₂ ⊢ B x)
--   → Δ ⊢ μ A x
--   → Δ₁ ⊗ Δ ⊗ Δ₂ ⊢ B x
-- μ-elimP {X = X}{Δ₁ = Δ₁}{Δ₂ = Δ₂}{A = A}{B = B}{x = x} f e =
--   ⊸-intro⁻ (⟜-intro⁻ (μ-elim {B = λ x → (Δ₁ ⊸ B x) ⟜ Δ₂}
--   (λ x → ⟜-intro (⊸-intro {!!})) e))
