open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.CanonicitySemantics (Σ₀ : hSet _) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List as List
open import Cubical.Data.Unit

import Metatheory.Syntax Σ₀ as Syntax
open import Grammar Σ₀
open import Grammar.KleeneStar Σ₀
open import Grammar.Equivalence Σ₀
open import Term Σ₀

-- the dependent types are interpreted as families over *closed* terms
⟦_⟧ctx : (Δ : Syntax.Ctx) → Syntax.Subst Syntax.· Δ → Type ℓ-zero
⟦_⟧subst : ∀ {Δ Δ'} → (δ' : Syntax.Subst Δ Δ') → ∀ δ → ⟦ Δ ⟧ctx δ → ⟦ Δ' ⟧ctx (δ' Syntax.∘ δ)
⟦_⟧ty : ∀ {Δ} → (A : Syntax.Ty Δ) → ∀ δ → ⟦ Δ ⟧ctx δ → Syntax.Tm Syntax.· (A Syntax.[ δ ]) → Type ℓ-zero
⟦_⟧tm : ∀ {Δ A} → (M : Syntax.Tm Δ A) → ∀ δ → (δ~ : ⟦ Δ ⟧ctx δ) → ⟦ A ⟧ty δ δ~ (M Syntax.[ δ ])



⟦_⟧gctx : ∀ {Δ} → (Γ : Syntax.GCtx Δ) → ∀ δ → ⟦ Δ ⟧ctx δ → Grammar ℓ-zero
⟦_⟧gctx' : ∀ {Δ} → (Γ : Syntax.GCtx Δ) → (Syntax.Subst Syntax.· Δ) → Grammar ℓ-zero
⟦ Γ ⟧gctx' δ w = Syntax.GSubst Syntax.⌈ w ⌉ (Γ Syntax.[ δ ])
⟦_⟧gctx-π : ∀ {Δ} → (Γ : Syntax.GCtx Δ) → ∀ δ → (δ~ : ⟦ Δ ⟧ctx δ)
  → ⟦ Γ ⟧gctx δ δ~ ⊢ ⟦ Γ ⟧gctx' δ


⟦_⟧gty : ∀ {Δ} → (A : Syntax.GTy Δ) → ∀ δ → ⟦ Δ ⟧ctx δ → Grammar ℓ-zero
⟦_⟧gty' : ∀ {Δ} → (A : Syntax.GTy Δ) → (Syntax.Subst Syntax.· Δ) → Grammar ℓ-zero
⟦ A ⟧gty' δ w = Syntax.GTm Syntax.⌈ w ⌉ (A Syntax.[ δ ])
⟦_⟧gty-π : ∀ {Δ} → (A : Syntax.GTy Δ) → ∀ δ → (δ~ : ⟦ Δ ⟧ctx δ)
  → ⟦ A ⟧gty δ δ~ ⊢ ⟦ A ⟧gty' δ

-- ⟦_⟧gty  : ∀ {Δ} → Syntax.GTy Δ → ⟦ Δ ⟧ctx → Grammar ℓ-zero
-- ⟦_⟧gsubst : ∀ {Δ Γ Γ'} → Syntax.GSubst Γ Γ' → (δ : ⟦ Δ ⟧ctx) → ⟦ Γ ⟧gctx δ ⊢ ⟦ Γ' ⟧gctx δ
-- ⟦_⟧gtm : ∀ {Δ Γ A} → Syntax.GTm Γ A → (δ : ⟦ Δ ⟧ctx) → ⟦ Γ ⟧gctx δ ⊢ ⟦ A ⟧gty δ

⟦ Syntax.· ⟧ctx δ = Unit
⟦ Δ Syntax., A ⟧ctx δ =
  Σ[ δ1~ ∈ ⟦ Δ ⟧ctx δ1 ]
  ⟦ A ⟧ty δ1 δ1~
    (subst (Syntax.Tm Syntax.·)
           (Syntax.subst-∘ A Syntax.π₁ δ)
           (Syntax.var Syntax.[ δ ]))
  where
    δ1 = Syntax.π₁ Syntax.∘ δ

⟦ Syntax.bit ⟧ty δ δ~ M =
  (M ≡ (Syntax.tru Syntax.[ δ ]))
  ⊎ ((M ≡ (Syntax.fls Syntax.[ δ ])))
⟦ A Syntax.[ δ' ] ⟧ty δ δ~ M =
  ⟦ A ⟧ty (δ' Syntax.∘ δ)
          (⟦ δ' ⟧subst δ δ~)
          (subst (Syntax.Tm Syntax.·)
                 (Syntax.subst-∘ A δ' δ)
                 M)
⟦ Syntax.subst-∘ A δ' δ'' i ⟧ty δ δ~ M = ⟦ A ⟧ty (Syntax.∘∘ δ δ'' δ' (~ i))
  {!!} -- this one is by a path and its inverse canceling
  {!!} -- this one needs an equation relating ∘∘ and subst-∘

⟦ Syntax.id ⟧subst δ δ~ = subst (⟦ _ ⟧ctx) (sym (Syntax.id∘ δ)) δ~
⟦ δ' Syntax.∘ δ'' ⟧subst δ δ~ =
  subst
    (⟦ _ ⟧ctx)
    (sym (Syntax.∘∘ δ δ'' δ'))
    (⟦ δ' ⟧subst (δ'' Syntax.∘ δ) (⟦ δ'' ⟧subst δ δ~))
⟦ Syntax.· ⟧subst δ δ~ = tt
⟦ δ' Syntax., M ⟧subst δ δ~ = {!!}
⟦ Syntax.π₁ ⟧subst δ δ~ = δ~ .fst
-- the following need "triangle/pentagon laws I think"
⟦ Syntax.id∘ δ' i ⟧subst δ δ~ = {!!}
⟦ Syntax.∘id δ' i ⟧subst δ δ~ = {!!}
⟦ Syntax.∘∘ δ' δ'' δ''' i ⟧subst δ δ~ = {!!}
-- ⟦_⟧gctx : ∀ {Δ} → Syntax.GCtx Δ → ⟦ Δ ⟧ctx → Grammar ℓ-zero
-- ⟦_⟧gty  : ∀ {Δ} → Syntax.GTy Δ → ⟦ Δ ⟧ctx → Grammar ℓ-zero
-- ⟦_⟧gsubst : ∀ {Δ Γ Γ'} → Syntax.GSubst Γ Γ' → (δ : ⟦ Δ ⟧ctx) → ⟦ Γ ⟧gctx δ ⊢ ⟦ Γ' ⟧gctx δ
-- ⟦_⟧gtm : ∀ {Δ Γ A} → Syntax.GTm Γ A → (δ : ⟦ Δ ⟧ctx) → ⟦ Γ ⟧gctx δ ⊢ ⟦ A ⟧gty δ

⟦ A Syntax.[ δ' ] ⟧gty δ δ~ = ⟦ A ⟧gty (δ' Syntax.∘ δ) (⟦ δ' ⟧subst δ δ~)
⟦ Syntax.lit c ⟧gty δ δ~ = literal c
⟦ Syntax.ε ⟧gty δ δ~ = ε
⟦ A₁ Syntax.⊗ A₂ ⟧gty δ δ~ = ⟦ A₁ ⟧gty δ δ~ ⊗ ⟦ A₂ ⟧gty δ δ~
⟦ A Syntax.⊸ B ⟧gty δ δ~ = ⟦ A ⟧gty δ δ~ ⊸ ⟦ B ⟧gty δ δ~
⟦ B Syntax.⟜ A ⟧gty δ δ~ = ⟦ B ⟧gty δ δ~ ⟜ ⟦ A ⟧gty δ δ~
⟦ Syntax.⊥ ⟧gty δ δ~ = ⊥-grammar
⟦ A Syntax.⊕ B ⟧gty δ δ~ = ⟦ A ⟧gty δ δ~ ⊕ ⟦ B ⟧gty δ δ~
⟦ Syntax.Star A ⟧gty δ δ~ = KL* (⟦ A ⟧gty δ δ~)

⟦ A Syntax.[ δ' ] ⟧gty-π δ δ~ = {!c!}
⟦ Syntax.lit c ⟧gty-π δ δ~ w w≡[c] =
  J (λ w [c]≡w → Syntax.GTm
      (List.rec Syntax.ε (λ c₁ → Syntax._⊗_ (Syntax.ty (Syntax.lit c₁)))
       w)
      (Syntax.lit c Syntax.[ δ ]))
  (subst (λ Γ → Syntax.GTm Γ (Syntax.lit c Syntax.[ δ ])) (((λ i → Syntax.ty (Syntax.lit c Syntax.[ Syntax.·-uniq δ Syntax.id i ])) ∙ λ i → Syntax.ty (Syntax.subst-id (Syntax.lit c) i)) ∙ sym Syntax.⊗ε) Syntax.GTm.var)
  -- (subst {!λ Γ → Syntax.GTm Γ (Syntax.lit c)!} {!!} Syntax.GTm.var)
  (sym w≡[c]) -- J {!!} {!!} {!!}

-- Goal: 

-- Goal: (w : Agda.Builtin.List.List (fst Σ₀)) →
      -- w ≡ (c Agda.Builtin.List.List.∷ Agda.Builtin.List.List.[]) →
      -- Syntax.GTm
      -- (Cubical.Data.List.Base.rec Syntax.ε
      --  (λ c₁ → Syntax._⊗_ (Syntax.ty (Syntax.lit c₁))) w)
      -- (Syntax.lit c Syntax.[ δ ])

⟦ Syntax.ε ⟧gty-π δ δ~ w w≡[] = J (λ w []≡w → ⟦ Syntax.ε ⟧gty' δ w)
  (subst
    (Syntax.GTm Syntax.ε)
    (sym (Syntax.subst-id Syntax.ε) ∙ (λ i → Syntax.ε Syntax.[ Syntax.·-uniq (Syntax.id) δ i ]))
    Syntax.⟨⟩)
  (sym w≡[])
⟦ A₁ Syntax.⊗ A₂ ⟧gty-π δ δ~ w (((w1 , w2) , w≡w1w2) , p1 , p2) =
  subst2 Syntax.GTm
    ((sym (Syntax.⌈++⌉ w1 w2) ∙ cong Syntax.⌈_⌉ (sym w≡w1w2)))
    {!!}
    (⟦ A₁ ⟧gty-π δ δ~ w1 p1 Syntax.,⊗ ⟦ A₂ ⟧gty-π δ δ~ w2 p2)
⟦ A Syntax.⊸ B ⟧gty-π δ δ~ = {!!}
⟦ B Syntax.⟜ A ⟧gty-π δ δ~ = {!!}
⟦ Syntax.⊥ ⟧gty-π δ δ~ = {!!}
⟦ A Syntax.⊕ B ⟧gty-π δ δ~ = {!!}
⟦ Syntax.Star A ⟧gty-π δ δ~ = {!!}
