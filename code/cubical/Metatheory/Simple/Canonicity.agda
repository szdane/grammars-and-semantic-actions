open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.Simple.Canonicity (Σ₀ : hSet _) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List as List
open import Cubical.Data.Unit

import Metatheory.Simple.Syntax Σ₀ as Syntax
open import Grammar Σ₀
open import Grammar.KleeneStar Σ₀
open import Grammar.Equivalence Σ₀
open import Term Σ₀

⟦_⟧ty : (A : Syntax.Ty) → Grammar ℓ-zero
⟦_⟧ty' : (A : Syntax.Ty) → Grammar ℓ-zero
⟦_⟧ty-π  : ∀ (A : Syntax.Ty) → ⟦ A ⟧ty ⊢ ⟦ A ⟧ty'
⟦_⟧ty-π⁻ : ∀ (A : Syntax.Ty) → ⟦ A ⟧ty' ⊢ ⟦ A ⟧ty

⟦_⟧ctx : (Γ : Syntax.Ctx) → Grammar ℓ-zero
⟦_⟧ctx' : (Γ : Syntax.Ctx) → Grammar ℓ-zero
⟦_⟧ctx-π  : ∀ (Γ : Syntax.Ctx) → ⟦ Γ ⟧ctx ⊢ ⟦ Γ ⟧ctx'
⟦_⟧ctx-π⁻ : ∀ (Γ : Syntax.Ctx) → ⟦ Γ ⟧ctx' ⊢ ⟦ Γ ⟧ctx

⟦_⟧tm : ∀ {Γ A} → Syntax.Tm Γ A → ⟦ Γ ⟧ctx ⊢ ⟦ A ⟧ty
⟦_⟧tm' : ∀ {Γ A} → Syntax.Tm Γ A → ⟦ Γ ⟧ctx' ⊢ ⟦ A ⟧ty'
⟦_⟧tm-π : ∀ {Γ A} (M : Syntax.Tm Γ A) → ⟦ A ⟧ty-π ∘g ⟦ M ⟧tm ≡ ⟦ M ⟧tm' ∘g ⟦ Γ ⟧ctx-π

⟦_⟧subst : ∀ {Γ Γ'} → Syntax.Subst Γ Γ' → ⟦ Γ ⟧ctx ⊢ ⟦ Γ' ⟧ctx
⟦_⟧subst' : ∀ {Γ Γ'} → Syntax.Subst Γ Γ' → ⟦ Γ ⟧ctx' ⊢ ⟦ Γ' ⟧ctx'
⟦_⟧subst-π : ∀ {Γ Γ'} (γ : Syntax.Subst Γ Γ') → ⟦ Γ' ⟧ctx-π ∘g ⟦ γ ⟧subst ≡ ⟦ γ ⟧subst' ∘g ⟦ Γ ⟧ctx-π

⟦ A ⟧ty' w = Syntax.Tm (Syntax.⌈ w ⌉) A
⟦ Γ ⟧ctx' w = Syntax.Subst (Syntax.⌈ w ⌉) Γ
⟦ M ⟧tm' w γ = M Syntax.[ γ ]
⟦ γ ⟧subst' w γ' = γ Syntax.∘s γ'

⟦ Syntax.lit c ⟧ty = literal c
⟦ Syntax.⊥ ⟧ty = ⊥-grammar
⟦ Syntax.ε ⟧ty = ε
⟦ A₁ Syntax.⊗ A₂ ⟧ty = ⟦ A₁ ⟧ty ⊗ ⟦ A₂ ⟧ty
 -- these are the "logical relations" cases and require a pullback of grammars. Return to these later
⟦ A Syntax.⊸ B ⟧ty = {!!}
⟦ B Syntax.⟜ A ⟧ty = {!!}
⟦ A Syntax.⊕ B ⟧ty = ⟦ A ⟧ty ⊕ ⟦ B ⟧ty
⟦ Syntax.Star A ⟧ty = KL* ⟦ A ⟧ty

⟦ Syntax.ty A ⟧ctx = ⟦ A ⟧ty
⟦ Syntax.εc ⟧ctx = ε
⟦ Γ₁ Syntax.⊗c Γ₂ ⟧ctx = ⟦ Γ₁ ⟧ctx ⊗ ⟦ Γ₂ ⟧ctx
⟦ Syntax.εc⊗c i ⟧ctx = {!!}
⟦ Syntax.⊗cεc i ⟧ctx = {!!}
⟦ Syntax.⊗c⊗c i ⟧ctx = {!!}

⟦ Syntax.lit c ⟧ty-π =
  literal-elim ((subst (λ Γ → Syntax.Tm Γ (Syntax.lit c)) (sym Syntax.⊗cεc) Syntax.var))
  -- J (λ w _ → ⟦ Syntax.lit c ⟧ty' w)
  -- (subst (λ Γ → Syntax.Tm Γ (Syntax.lit c)) (sym Syntax.⊗cεc) Syntax.var)
  -- (sym w≡[c])
⟦ Syntax.⊥ ⟧ty-π = ⊥-elim
⟦ Syntax.ε ⟧ty-π = ε-elim Syntax.⟨⟩
⟦ A₁ Syntax.⊗ A₂ ⟧ty-π =
  ⊗-elim (λ w1 w2 M₁ M₂ → (M₁ Syntax.,⊗ M₂) Syntax.[ Syntax.⌈++⌉-subst w1 w2 ])
  ∘g ⟦ A₁ ⟧ty-π ,⊗ ⟦ A₂ ⟧ty-π
⟦ A Syntax.⊸ B ⟧ty-π = {!!}
⟦ B Syntax.⟜ A ⟧ty-π = {!!}
⟦ A Syntax.⊕ B ⟧ty-π = ⊕-elim
  (λ w a → Syntax.inl Syntax.[ Syntax.tys (⟦ A ⟧ty-π w a) ])
  (λ w b → Syntax.inr Syntax.[ Syntax.tys (⟦ B ⟧ty-π w b) ])
⟦ Syntax.Star A ⟧ty-π = foldKL*r _ (record { the-ℓ = _ ; G = _
  ; nil-case = ε-elim Syntax.nil
  ; cons-case =
    ⊗-elim (λ w1 w2 M₁ M₂ → Syntax.cons Syntax.[ (Syntax.tys M₁ Syntax.,⊗s Syntax.tys M₂) Syntax.∘s Syntax.⌈++⌉-subst w1 w2 ])
    ∘g ⟦ A ⟧ty-π ,⊗ id
  })

⟦ Syntax.ty A ⟧ctx-π w M~ = Syntax.tys (⟦ A ⟧ty-π w M~)
⟦ Syntax.Ctx.εc ⟧ctx-π = ε-elim Syntax.ids
⟦ Γ₁ Syntax.⊗c Γ₂ ⟧ctx-π =
  ⊗-elim (λ w1 w2 γ1 γ2 → (γ1 Syntax.,⊗s γ2) Syntax.∘s Syntax.⌈++⌉-subst w1 w2)
  ∘g (⟦ Γ₁ ⟧ctx-π ,⊗ ⟦ Γ₂ ⟧ctx-π)
⟦ Syntax.Ctx.εc⊗c i ⟧ctx-π = {!!}
⟦ Syntax.Ctx.⊗cεc i ⟧ctx-π = {!!}
⟦ Syntax.Ctx.⊗c⊗c i ⟧ctx-π = {!!}


⟦ Syntax.var ⟧tm = id
⟦ M Syntax.[ γ ] ⟧tm = ⟦ M ⟧tm ∘g ⟦ γ ⟧subst
⟦ M₁ Syntax.,⊗ M₂ ⟧tm = ⟦ M₁ ⟧tm ,⊗ ⟦ M₂ ⟧tm
⟦ Syntax.⟨⟩ ⟧tm = id
⟦ Syntax.ε-L M ⟧tm = ⟦ M ⟧tm ∘g id ,⊗ ⊗-unit-l⁻ -- could also be done with subst
⟦ Syntax.⊗-L M ⟧tm = ⟦ M ⟧tm ∘g id ,⊗ ⊗-assoc -- could also be done with subst
⟦ Syntax.inl ⟧tm = ⊕-inl
⟦ Syntax.inr ⟧tm = ⊕-inr
⟦ Syntax.nil ⟧tm = nil
⟦ Syntax.cons ⟧tm = cons
-- refl :)
⟦ Syntax.subst-id M i ⟧tm = ⟦ M ⟧tm
⟦ Syntax.subst-∘ M γ γ' i ⟧tm = ⟦ M ⟧tm ∘g ⟦ γ ⟧subst ∘g ⟦ γ' ⟧subst
⟦ Syntax.var-tys M i ⟧tm = ⟦ M ⟧tm

⟦ Syntax.ids ⟧subst = id
⟦ γ' Syntax.∘s γ ⟧subst = ⟦ γ' ⟧subst ∘g ⟦ γ ⟧subst
⟦ γ₁ Syntax.,⊗s γ₂ ⟧subst = ⟦ γ₁ ⟧subst ,⊗ ⟦ γ₂ ⟧subst
⟦ Syntax.tys M ⟧subst = ⟦ M ⟧tm
-- these hold definitionally :)
⟦ Syntax.ids∘s γ i ⟧subst = ⟦ γ ⟧subst 
⟦ Syntax.∘s∘s γ γ' γ'' i ⟧subst = ⟦ γ'' ⟧subst ∘g ⟦ γ' ⟧subst ∘g ⟦ γ ⟧subst

⟦ Syntax.var {A = A} ⟧tm-π i w p = Syntax.var-tys (⟦ A ⟧ty-π w p) (~ i)
⟦ M Syntax.[ γ ] ⟧tm-π =
  (λ i → ⟦ M ⟧tm-π i ∘g ⟦ γ ⟧subst)
  ∙ (λ i → ⟦ M ⟧tm' ∘g ⟦ γ ⟧subst-π i)
  ∙ funExt λ w → funExt λ p → Syntax.subst-∘ M γ (⟦ _ ⟧ctx-π w p)
⟦ Syntax.⟨⟩ ⟧tm-π = {!!}
⟦ Syntax.ε-L M ⟧tm-π = {!!}
⟦ M₁ Syntax.,⊗ M₂ ⟧tm-π =
  (λ i → ⊗-elim (λ w1 w2 M₃ M₄ → (M₃ Syntax.,⊗ M₄) Syntax.[ Syntax.⌈++⌉-subst w1 w2 ]) ∘g ⟦ M₁ ⟧tm-π i ,⊗ ⟦ M₂ ⟧tm-π i)
  ∙ {!!}
⟦ Syntax.⊗-L M ⟧tm-π = {!!}
⟦ Syntax.inl ⟧tm-π = {!!}
⟦ Syntax.inr ⟧tm-π = {!!}
⟦ Syntax.nil ⟧tm-π = {!!}
⟦ Syntax.cons ⟧tm-π = {!!}
-- fillers once we have the grammars are sets
⟦ Syntax.subst-id M i ⟧tm-π = {!!}

⟦ Syntax.ids {Γ} ⟧subst-π i w p = Syntax.ids∘s (⟦ Γ ⟧ctx-π w p) (~ i)
⟦ Syntax._∘s_ {Γ}{Γ'}{Γ''} γ' γ ⟧subst-π = funExt λ w → funExt λ p →
  funExt⁻ (funExt⁻ ⟦ γ' ⟧subst-π w) _
  ∙ (λ i → γ' Syntax.∘s ⟦ γ ⟧subst-π i w p)
  ∙ λ i → Syntax.∘s∘s (⟦ Γ ⟧ctx-π w p) γ γ' (~ i)
⟦ γ₁ Syntax.,⊗s γ₂ ⟧subst-π = {!!}
⟦ Syntax.tys M ⟧subst-π = {!!}
-- These are trivial fillers, follow if all grammars are sets (they are)
⟦ Syntax.ids∘s γ i ⟧subst-π = {!!}
⟦ Syntax.∘s∘s γ γ' γ'' i ⟧subst-π = {!!}


⟦string⟧ : ∀ w → ⟦ Syntax.⌈ w ⌉ ⟧ctx w
⟦string⟧ = List.elim
  ε-intro
  λ {c}{w} ⟦⌈w⌉⟧ → ⊗-intro' [ c ] w refl ⟦⌈w⌉⟧ 
⟦string⟧-id : ∀ w → ⟦ Syntax.⌈ w ⌉ ⟧ctx-π w (⟦string⟧ w) ≡ Syntax.ids
⟦string⟧-id = List.elim
  (ε-β {g = ⟦ Syntax.⌈ [] ⌉ ⟧ctx'} Syntax.ids)
  -- (ε-β {g = {!!}} Syntax.ids)
  {!!}
  -- ((JRefl {x = []} (λ w _ → ⟦ Syntax.εc ⟧ctx' w) _))
  -- λ {c}{w'} ⟦string⟧⟨w'⟩≡ids → {!!}

-- these are the "canonicalization" functions: they take in terms of type ⌈ w ⌉ ⊢ M : A and output ⟦ A ⟧ty w
⟦ A ⟧ty-π⁻ w M = ⟦ M ⟧tm w (⟦string⟧ w)
⟦ Γ ⟧ctx-π⁻ w γ = ⟦ γ ⟧subst w (⟦string⟧ w)

tm-canonicity : ∀ A → StrongEquivalence ⟦ A ⟧ty ⟦ A ⟧ty'
tm-canonicity A = mkStrEq ⟦ A ⟧ty-π ⟦ A ⟧ty-π⁻
  (funExt (λ w → funExt λ M →
    (λ i → ⟦ M ⟧tm-π i w (⟦string⟧ w))
    ∙ (λ i → M Syntax.[ ⟦string⟧-id w i ])
    ∙ Syntax.subst-id M))
  (funExt λ w → funExt λ p → {!!}) -- this would require another proof by induction, methinks
