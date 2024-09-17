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

⟦ Syntax.lit c ⟧ty-π w w≡[c] = J (λ w _ → ⟦ Syntax.lit c ⟧ty' w)
  (subst (λ Γ → Syntax.Tm Γ (Syntax.lit c)) (sym Syntax.⊗cεc) Syntax.var)
  (sym w≡[c])
⟦ Syntax.⊥ ⟧ty-π = ⊥-elim
⟦ Syntax.ε ⟧ty-π w w≡[] = J (λ w _ → ⟦ Syntax.ε ⟧ty' w)
  Syntax.⟨⟩
  (sym w≡[])
⟦ A₁ Syntax.⊗ A₂ ⟧ty-π w (((w1 , w2) , w≡w1w2) , p1 , p2) =
  J (λ w _ → ⟦ A₁ Syntax.⊗ A₂ ⟧ty' w)
  (subst (λ Γ → Syntax.Tm Γ _)
    (sym (Syntax.⌈++⌉ w1 w2))
    (⟦ A₁ ⟧ty-π w1 p1 Syntax.,⊗ ⟦ A₂ ⟧ty-π w2 p2))
  (sym w≡w1w2)
⟦ A Syntax.⊸ B ⟧ty-π = {!!}
⟦ B Syntax.⟜ A ⟧ty-π = {!!}
⟦ A Syntax.⊕ B ⟧ty-π = ⊕-elim
  (λ w a → Syntax.inl Syntax.[ Syntax.tys (⟦ A ⟧ty-π w a) ])
  (λ w b → Syntax.inr Syntax.[ Syntax.tys (⟦ B ⟧ty-π w b) ])
⟦ Syntax.Star A ⟧ty-π = foldKL*r _ (record { the-ℓ = _ ; G = _
  ; nil-case = λ w w≡[] → J (λ w _ → ⟦ Syntax.Star A ⟧ty' w)
    Syntax.nil
    (sym w≡[])
  ; cons-case = λ w (((w1 , w2) , w≡w1w2) , p1 , p2) → J (λ w _ → ⟦ Syntax.Star A ⟧ty' w)
    (subst (λ Γ → Syntax.Tm Γ _)
     ((sym (Syntax.⌈++⌉ w1 w2)))
     (Syntax.cons Syntax.[ Syntax.tys (⟦ A ⟧ty-π w1 p1) Syntax.,⊗s Syntax.tys p2 ]))
    (sym w≡w1w2) })

⟦ Syntax.ty A ⟧ctx-π w M~ = Syntax.tys (⟦ A ⟧ty-π w M~)
⟦ Syntax.Ctx.εc ⟧ctx-π w w≡[] = J (λ w _ → ⟦ Syntax.εc ⟧ctx' w)
  Syntax.ids
  (sym w≡[])
⟦ Γ₁ Syntax.⊗c Γ₂ ⟧ctx-π w (((w1 , w2) , w≡w1w2) , p1 , p2) =
  J (λ w _ → ⟦ Γ₁ Syntax.⊗c Γ₂ ⟧ctx' w)
  (subst (λ ⌈w⌉ → Syntax.Subst ⌈w⌉ _) (sym (Syntax.⌈++⌉ w1 w2))
    (⟦ Γ₁ ⟧ctx-π w1 p1 Syntax.,⊗s ⟦ Γ₂ ⟧ctx-π w2 p2))
  (sym w≡w1w2)
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
⟦ M₁ Syntax.,⊗ M₂ ⟧tm-π =
  {!!} ∙ {!!}
⟦ Syntax.⟨⟩ ⟧tm-π = {!!}
⟦ Syntax.ε-L M ⟧tm-π = {!!}
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
⟦string⟧ = List.elim (refl {x = []}) λ {c}{w'} ⟦w'⟧ → (splitChar c w') , (refl , ⟦w'⟧)

⟦string⟧-id : ∀ w → ⟦ Syntax.⌈ w ⌉ ⟧ctx-π w (⟦string⟧ w) ≡ Syntax.ids
⟦string⟧-id = List.elim
  ((JRefl {x = []} (λ w _ → ⟦ Syntax.εc ⟧ctx' w) _))
  λ {c}{w'} ⟦string⟧⟨w'⟩≡ids → {!!}

-- these are the "canonicalization" functions: they take in terms of type ⌈ w ⌉ ⊢ M : A and output ⟦ A ⟧ty w
⟦ A ⟧ty-π⁻ w M = ⟦ M ⟧tm w (⟦string⟧ w)
⟦ Γ ⟧ctx-π⁻ w γ = ⟦ γ ⟧subst w (⟦string⟧ w)

tm-canonicity : ∀ A → StrongEquivalence ⟦ A ⟧ty ⟦ A ⟧ty'
tm-canonicity A = mkStrEq ⟦ A ⟧ty-π ⟦ A ⟧ty-π⁻
  (funExt (λ w → funExt λ M →
    (λ i → ⟦ M ⟧tm-π i w (⟦string⟧ w))
    ∙ (λ i → M Syntax.[ ⟦string⟧-id w i ])
    ∙ Syntax.subst-id M))
  (funExt λ w → funExt λ p → {!!}) -- this will require another proof by induction, methinks
