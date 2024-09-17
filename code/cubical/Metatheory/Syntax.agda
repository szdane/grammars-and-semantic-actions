open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.Syntax (Σ₀ : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.FinData
open import Cubical.Data.Unit

open import String.Base Σ₀ public
private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓx ℓy ℓb ℓg ℓg' ℓh ℓh' : Level

module _ where
  data Ctx : Type ℓ-zero
  data Subst : (Δ : Ctx) → Ctx → Type ℓ-zero
  data Ty : Ctx → Type ℓ-zero
  data Tm  : (Δ : Ctx) → (Ty Δ) → Type ℓ-zero

  data Ctx where
    · : Ctx
    _,_ : (Δ : Ctx) → Ty Δ → Ctx

  _∘subst_ : ∀ {Θ Δ Γ} → Subst Θ Γ → Subst Δ Θ → Subst Δ Γ
  ids : ∀ {Δ} → Subst Δ Δ
  data Ty where
    bit : Ty ·
    _[_] : ∀ {Δ Δ'} → Ty Δ → Subst Δ' Δ → Ty Δ'
    subst-∘ : ∀ {Δ Δ' Δ''} → ∀ A → (δ' : Subst Δ' Δ'')(δ : Subst Δ Δ')
      → (A [ δ' ] [ δ ]) ≡
      (A [ δ' ∘subst δ ])
    subst-id : ∀ {Δ} (A : Ty Δ) → A [ ids ] ≡ A

  -- A [ δ'' ] [ δ' ] [ δ ]
  -- ≡ A [ δ'' ] [ δ' ∘ δ ]
  -- ≡ A [ δ'' ∘ δ' ∘ δ ]
  --
  -- vs
  -- A [ δ'' ] [ δ' ] [ δ ]
  -- ≡ A [ δ'' ∘ δ' ] [ δ ]
  -- ≡ A [ (δ'' ∘ δ') ∘ δ ]
  -- ≡ A [ δ'' ∘ δ' ∘ δ ]
  --
  -- pentagon law?
  data Subst where
    · : ∀ {Δ} → Subst Δ ·
    _,_ : ∀ {Γ Δ A} → (γ : Subst Δ Γ) → (Tm Δ (A [ γ ])) → Subst Δ Γ
    id  : ∀ {Δ} → Subst Δ Δ
    _∘_ : ∀ {Θ Δ Γ} → Subst Θ Γ → Subst Δ Θ → Subst Δ Γ
    π₁ : ∀ {Δ A} → Subst (Δ , A) Δ

    id∘ : ∀ {Δ Δ'}(δ : Subst Δ Δ') → id ∘ δ ≡ δ
    ∘id : ∀ {Δ Δ'}(δ : Subst Δ Δ') → δ ∘ id ≡ δ
    ∘∘ : ∀ {Δ Δ' Δ'' Δ'''}(δ : Subst Δ Δ')(δ' : Subst Δ' Δ'')(δ'' : Subst Δ'' Δ''')
      → (δ'' ∘ δ') ∘ δ ≡ δ'' ∘ (δ' ∘ δ)
    ·-uniq : ∀ {Δ} (δ δ' : Subst Δ ·) → δ ≡ δ'
  _∘subst_ = _∘_
  ids = id

  data Tm where
    var : ∀ {Δ A} → Tm (Δ , A) (A [ π₁ ])
    _[_] : ∀ {Δ Γ A} → Tm Γ A → (γ : Subst Δ Γ) → Tm Δ (A [ γ ])
    tru fls : Tm · bit

  data GTy : ∀ (Δ : Ctx) → Type ℓ-zero where
    lit : ⟨ Σ₀ ⟩ → GTy ·
    ε : GTy ·
    _⊗_ : ∀ {Δ} → GTy Δ → GTy Δ → GTy Δ
    _⊸_ : ∀ {Δ} →  GTy Δ → GTy Δ → GTy Δ
    _⟜_ : ∀ {Δ} → GTy Δ → GTy Δ → GTy Δ
    ⊥ : GTy ·
    _⊕_ : ∀ {Δ} → GTy Δ → GTy Δ → GTy Δ
    Star : ∀ {Δ} → GTy Δ → GTy Δ
    _[_] : ∀ {Δ Δ'} → GTy Δ' → Subst Δ Δ' → GTy Δ
    subst-id : ∀ {Δ} (A : GTy Δ) → A [ ids ] ≡ A

  -- todo: full on bunches
  data GCtx (Δ : Ctx) : Type ℓ-zero where
    ε : GCtx Δ
    _⊗_ : GCtx Δ → GCtx Δ → GCtx Δ
    ε⊗ : ∀ {A} → ε ⊗ A ≡ A
    ⊗ε : ∀ {A} → A ⊗ ε ≡ A
    ⊗⊗ : ∀ {A B C} → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)
    ty : GTy Δ → GCtx Δ
    _[_] : ∀ {Δ'} → GCtx Δ' → Subst Δ Δ' → GCtx Δ
    -- presheaf laws for _[_]?
    -- pentagon/triangle laws?
  infixr 5 _⊗_

  data GSubst {Δ : Ctx} : GCtx Δ → GCtx Δ → Type ℓ-zero where
    id : ∀ {Γ} → GSubst Γ Γ
    _∘_ : ∀ {Γ Γ' Γ''} → GSubst Γ' Γ'' → GSubst Γ Γ' → GSubst Γ Γ''
    _,⊗_ : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'}
      → GSubst Γ₁ Γ₁' → GSubst Γ₂ Γ₂'
      → GSubst (Γ₁ ⊗ Γ₂) (Γ₁' ⊗ Γ₂')
    -- todo: equations?

  data GTm : ∀ {Δ : Ctx} → GCtx Δ → GTy Δ → Type ℓ-zero where
    _[_] : ∀ {Δ Δ'}{Γ : GCtx Δ'}{A} → GTm Γ A → ∀ δ → GTm {Δ} (Γ [ δ ]) (A [ δ ])
    var : ∀ {Δ A} → GTm {Δ} (ty A) A
    _[_]l : ∀ {Δ Γ Γ' A} → GTm {Δ} Γ A → GSubst Γ' Γ → GTm Γ' A
    ⟨⟩ : GTm ε ε
    ε-L : ∀ {Δ Γ₁ Γ₂ Γ}
      → GTm {Δ} (Γ₁ ⊗ ty ε [ · ] ⊗ Γ₂) Γ
      → GTm (Γ₁ ⊗ Γ₂) Γ
    _,⊗_ : ∀ {Δ Γ₁ Γ₂ A₁ A₂} → GTm Γ₁ A₁ → GTm Γ₂ A₂ → GTm {Δ} (Γ₁ ⊗ Γ₂) (A₁ ⊗ A₂)
    -- ⊗-L : ∀ {Γ₁ A₁ A₂ Γ₂ Γ'}
    --   → GTm (Γ₁ ⊗ ty (A₁ ⊗ A₂) ⊗ Γ₂) Γ'
    --   → GTm (Γ₁ ⊗ ty A₁ ⊗ ty A₂ ⊗ Γ₂) Γ'
    -- ⊸-app : ∀ {A B} → GTm (ty A ⊗ ty (A ⊸ B)) B
    -- ⊸-intro : ∀ {Γ A B}
    --   → GTm (ty A ⊗ Γ) B
    --   → GTm Γ (A ⊸ B)
    -- ⟜-app : ∀ {A B} → GTm (ty (B ⟜ A) ⊗ ty A) B
    -- ⟜-intro : ∀ {Γ A B}
    --   → GTm (Γ ⊗ ty A) B
    --   → GTm Γ (B ⟜ A)
    -- -- ⊥-L : ∀ {Γ₁ Γ₂ A} → GTm (Γ₁ ⊗ ty ⊥ ⊗ Γ₂) A
    -- inl : ∀ {A B} → GTm (ty A) (A ⊕ B)
    -- inr : ∀ {A B} → GTm (ty B) (A ⊕ B)
    -- ⊕-L : ∀ {Γ₁ Γ₂ A B C}
    --   → GTm (Γ₁ ⊗ ty A ⊗ Γ₂) C
    --   → GTm (Γ₁ ⊗ ty B ⊗ Γ₂) C
    --   → GTm (Γ₁ ⊗ ty (A ⊕ B) ⊗ Γ₂) C

    -- nil : ∀ {A} → GTm ε (Star A)
    -- cons : ∀ {A} → GTm (ty A ⊗ ty (Star A)) (Star A)
    -- -- todo: more general version? e.g., parameterized?
    -- fold : ∀ {A C} → GTm ε C → GTm (ty A ⊗ ty C) C
    --   → GTm (ty (Star A)) C

    -- TODO: equations?
⌈_⌉ : String → GCtx ·
⌈ w ⌉ = List.rec ε (λ c ⌈w'⌉ → ty (lit c) ⊗ ⌈w'⌉) w
⌈++⌉ : ∀ w1 w2 → ⌈ w1 ++ w2 ⌉ ≡ ⌈ w1 ⌉ ⊗ ⌈ w2 ⌉
⌈++⌉ [] w2 = sym ε⊗
⌈++⌉ (c ∷ w1) w2 = cong (ty (lit c) ⊗_) (⌈++⌉ w1 w2) ∙ sym ⊗⊗
