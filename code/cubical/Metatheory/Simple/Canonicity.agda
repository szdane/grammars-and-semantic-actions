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
open import Metatheory.Simple.ClosedTerms Σ₀
open import Grammar Σ₀
open import Grammar.Equivalence Σ₀
open import Term Σ₀

-- We define grammars of canonical forms for (closed) terms and substitutions
CanonicalTm : (A : Syntax.Ty) → Grammar ℓ-zero
CanonicalSubst : (Γ : Syntax.Ctx) → Grammar ℓ-zero
-- Every Canonical term/substitution can be viewed as an actual closed term/substitution
AsClosedTm : (A : Syntax.Ty) → CanonicalTm A ⊢ ClosedTm A
AsClosedSubst : (Γ : Syntax.Ctx) → CanonicalSubst Γ ⊢ ClosedSubst Γ
-- We want to show that canonical forms are closed under substitution into an *arbitrary* term.
-- This will be enough to establish that every closed term has a canonical form.
-- First, we define the action of substitution of a canonical form into a syntactic term/subst
can-tm : ∀ {Γ A} (M : Syntax.Tm Γ A) → CanonicalSubst Γ ⊢ CanonicalTm A
can-subst : ∀ {Γ' Γ} (γ : Syntax.Subst Γ' Γ) → CanonicalSubst Γ' ⊢ CanonicalSubst Γ
-- Then we must show that this action of substituting a canonical
-- subst into a term produces a canonical form *for* the substituted
-- term:
can-tm-correct : ∀ {Γ A} (M : Syntax.Tm Γ A)
  → AsClosedTm A ∘g can-tm M ≡ close-tm M ∘g AsClosedSubst Γ
can-subst-correct : ∀ {Γ' Γ} (γ : Syntax.Subst Γ' Γ)
  → AsClosedSubst Γ ∘g can-subst γ ≡ close-subst γ ∘g AsClosedSubst Γ'

-- For regular and context-free grammars, the types of canonical forms
-- match the grammar semantics exactly. It's for the functions (TODO) that things diverge
CanonicalTm (Syntax.lit c) = literal c
CanonicalTm Syntax.⊥ = ⊥
CanonicalTm Syntax.ε = ε
CanonicalTm (A₁ Syntax.⊗ A₂) = CanonicalTm A₁ ⊗ CanonicalTm A₂
CanonicalTm (A₁ Syntax.⊕ A₂) = CanonicalTm A₁ ⊕ CanonicalTm A₂
CanonicalTm (Syntax.Star A) = KL* (CanonicalTm A)

CanonicalSubst (Syntax.ty A) = CanonicalTm A
CanonicalSubst Syntax.εc = ε
CanonicalSubst (Γ Syntax.⊗c Γ₁) = CanonicalSubst Γ ⊗ CanonicalSubst Γ₁
CanonicalSubst (Syntax.εc⊗c {Γ} i) = StrongEquivalence→Path {h = CanonicalSubst Γ} ⊗-unit-l-StrEq i
CanonicalSubst (Syntax.⊗cεc {Γ} i) = StrongEquivalence→Path {h = CanonicalSubst Γ} ⊗-unit-r-StrEq i
CanonicalSubst (Syntax.⊗c⊗c {Γ₁}{Γ₂}{Γ₃} i) =
  StrongEquivalence→Path
    (⊗-assoc-StrEq {g = CanonicalSubst Γ₁}
                   {h = CanonicalSubst Γ₂}
                   {k = CanonicalSubst Γ₃})
                   i

AsClosedTm (Syntax.lit c) = literal-elim (litTm Syntax.var)
AsClosedTm Syntax.⊥ = ⊥-elim
AsClosedTm Syntax.ε = lax-tyε
AsClosedTm (A₁ Syntax.⊗ A₂) = lax-ty⊗ ∘g AsClosedTm A₁ ,⊗ AsClosedTm A₂
AsClosedTm (A₁ Syntax.⊕ A₂) =
  ⊕-elim
    (close-tm Syntax.inl ∘g close-tys ∘g AsClosedTm A₁)
    (close-tm Syntax.inr ∘g close-tys ∘g AsClosedTm A₂)
AsClosedTm (Syntax.Star A) = foldKL*r _ (record { the-ℓ = _ ; G = _
  ; nil-case = ε-elim (εTm Syntax.nil)
  ; cons-case =
    close-tm Syntax.cons ∘g lax-ctx⊗ ∘g (close-tys ∘g AsClosedTm A) ,⊗ close-tys
  })

AsClosedSubst (Syntax.ty A) = close-tys ∘g AsClosedTm A
AsClosedSubst Syntax.εc = lax-ctxε
AsClosedSubst (Γ Syntax.⊗c Γ₁) = lax-ctx⊗ ∘g AsClosedSubst Γ ,⊗ AsClosedSubst Γ₁
-- What is this goal saying exactly?
-- It's a commuting square essentially
--
-- (lax-ctx ∘g ε-elim (εSubst Syntax.ids) ,⊗ AsClosedSubst Γ) : εc ⊗ CanonicalSubst Γ ⊢ ClosedSubst (εc ⊗c Γ)
-- =~
-- AsClosedSubst Γ : CanonicalSubst Γ ⊢ ClosedSubst Γ
--
-- modulo εc ⊗ CanonicalSubst Γ ≡ CanonicalSubst Γ and ClosedSubst (εc ⊗c Γ) ≡ ClosedSubst Γ
--
-- Proving these is *precisely* showing the assoc and unit laws for a lax monoidal functor
AsClosedSubst (Syntax.εc⊗c i) = {!!}
AsClosedSubst (Syntax.⊗cεc i) = {!!}
AsClosedSubst (Syntax.⊗c⊗c i) = {!!}

-- ⟦_⟧ty : (A : Syntax.Ty) → Grammar ℓ-zero
-- ⟦_⟧ty-π  : ∀ (A : Syntax.Ty) → ⟦ A ⟧ty ⊢ ClosedTm A

-- ⟦_⟧ctx : (Γ : Syntax.Ctx) → Grammar ℓ-zero
-- ⟦_⟧ctx-π  : ∀ (Γ : Syntax.Ctx) → ⟦ Γ ⟧ctx ⊢ ClosedSubst Γ

-- ⟦_⟧tm : ∀ {Γ A} → Syntax.Tm Γ A → ⟦ Γ ⟧ctx ⊢ ⟦ A ⟧ty
-- ⟦_⟧tm-π : ∀ {Γ A} (M : Syntax.Tm Γ A) → ⟦ A ⟧ty-π ∘g ⟦ M ⟧tm ≡ close-tm M ∘g ⟦ Γ ⟧ctx-π

-- ⟦_⟧subst : ∀ {Γ Γ'} → Syntax.Subst Γ Γ' → ⟦ Γ ⟧ctx ⊢ ⟦ Γ' ⟧ctx
-- ⟦_⟧subst-π : ∀ {Γ Γ'} (γ : Syntax.Subst Γ Γ') → ⟦ Γ' ⟧ctx-π ∘g ⟦ γ ⟧subst ≡ close-subst γ ∘g ⟦ Γ ⟧ctx-π

-- ⟦ Syntax.lit c ⟧ty = literal c
-- ⟦ Syntax.⊥ ⟧ty = ⊥
-- ⟦ Syntax.ε ⟧ty = ε
-- ⟦ A₁ Syntax.⊗ A₂ ⟧ty = ⟦ A₁ ⟧ty ⊗ ⟦ A₂ ⟧ty
-- --  -- these are the "logical relations" cases and require a pullback of grammars. Return to these later
-- -- ⟦ A Syntax.⊸ B ⟧ty = {!!}
-- -- ⟦ B Syntax.⟜ A ⟧ty = {!!}
-- ⟦ A Syntax.⊕ B ⟧ty = ⟦ A ⟧ty ⊕ ⟦ B ⟧ty
-- ⟦ Syntax.Star A ⟧ty = KL* ⟦ A ⟧ty

-- ⟦ Syntax.ty A ⟧ctx = ⟦ A ⟧ty
-- ⟦ Syntax.εc ⟧ctx = ε
-- ⟦ Γ₁ Syntax.⊗c Γ₂ ⟧ctx = ⟦ Γ₁ ⟧ctx ⊗ ⟦ Γ₂ ⟧ctx
-- ⟦ Syntax.εc⊗c i ⟧ctx = {!!}
-- ⟦ Syntax.⊗cεc i ⟧ctx = {!!}
-- ⟦ Syntax.⊗c⊗c i ⟧ctx = {!!}

-- ⟦ Syntax.lit c ⟧ty-π = literal-elim (litTm Syntax.var)
-- ⟦ Syntax.⊥ ⟧ty-π = ⊥-elim
-- ⟦ Syntax.ε ⟧ty-π = ε-elim (εTm Syntax.⟨⟩) -- ε-elim Syntax.⟨⟩
-- ⟦ A₁ Syntax.⊗ A₂ ⟧ty-π =
--   lax-ty ∘g ⟦ A₁ ⟧ty-π ,⊗ ⟦ A₂ ⟧ty-π
-- -- ⟦ A Syntax.⊸ B ⟧ty-π = {!!}
-- -- ⟦ B Syntax.⟜ A ⟧ty-π = {!!}
-- ⟦ A Syntax.⊕ B ⟧ty-π = ⊕-elim
--   (close-tm Syntax.inl ∘g close-tys ∘g ⟦ A ⟧ty-π)
--   (close-tm Syntax.inr ∘g close-tys ∘g ⟦ B ⟧ty-π)
-- ⟦ Syntax.Star A ⟧ty-π = foldKL*r _ (record { the-ℓ = _ ; G = _
--   ; nil-case = ε-elim (εTm Syntax.nil) -- ε-elim Syntax.nil
--   ; cons-case = close-tm Syntax.cons ∘g lax-ctx ∘g (close-tys ∘g ⟦ A ⟧ty-π) ,⊗ close-tys
--     -- ⊗-elim (λ w1 w2 M₁ M₂ → Syntax.cons Syntax.[ (Syntax.tys M₁ Syntax.,⊗s Syntax.tys M₂) Syntax.∘s Syntax.⌈++⌉-subst w1 w2 ])
--     -- ∘g ⟦ A ⟧ty-π ,⊗ id
--   })

-- ⟦ Syntax.ty A ⟧ctx-π = {!!} -- Syntax.tys (⟦ A ⟧ty-π w M~)
-- ⟦ Syntax.Ctx.εc ⟧ctx-π = {!!} -- ε-elim Syntax.ids
-- ⟦ Γ₁ Syntax.⊗c Γ₂ ⟧ctx-π = lax-ctx ∘g (⟦ Γ₁ ⟧ctx-π ,⊗ ⟦ Γ₂ ⟧ctx-π)
-- ⟦ Syntax.Ctx.εc⊗c i ⟧ctx-π = {!!}
-- ⟦ Syntax.Ctx.⊗cεc i ⟧ctx-π = {!!}
-- ⟦ Syntax.Ctx.⊗c⊗c i ⟧ctx-π = {!!}


-- ⟦ Syntax.var ⟧tm = id
-- ⟦ M Syntax.[ γ ] ⟧tm = ⟦ M ⟧tm ∘g ⟦ γ ⟧subst
-- ⟦ M₁ Syntax.,⊗ M₂ ⟧tm = ⟦ M₁ ⟧tm ,⊗ ⟦ M₂ ⟧tm
-- ⟦ Syntax.⟨⟩ ⟧tm = id
-- ⟦ Syntax.ε-L M ⟧tm = ⟦ M ⟧tm ∘g id ,⊗ ⊗-unit-l⁻ -- could also be done with subst
-- ⟦ Syntax.⊗-L M ⟧tm = ⟦ M ⟧tm ∘g id ,⊗ ⊗-assoc -- could also be done with subst
-- ⟦ Syntax.inl ⟧tm = ⊕-inl
-- ⟦ Syntax.inr ⟧tm = ⊕-inr
-- ⟦ Syntax.nil ⟧tm = nil
-- ⟦ Syntax.cons ⟧tm = cons
-- -- refl :)
-- ⟦ Syntax.subst-id M i ⟧tm = ⟦ M ⟧tm
-- ⟦ Syntax.subst-∘ M γ γ' i ⟧tm = ⟦ M ⟧tm ∘g ⟦ γ ⟧subst ∘g ⟦ γ' ⟧subst
-- ⟦ Syntax.var-tys M i ⟧tm = ⟦ M ⟧tm

-- ⟦ Syntax.ids ⟧subst = id
-- ⟦ γ' Syntax.∘s γ ⟧subst = ⟦ γ' ⟧subst ∘g ⟦ γ ⟧subst
-- ⟦ γ₁ Syntax.,⊗s γ₂ ⟧subst = ⟦ γ₁ ⟧subst ,⊗ ⟦ γ₂ ⟧subst
-- ⟦ Syntax.tys M ⟧subst = ⟦ M ⟧tm
-- -- these hold definitionally :)
-- ⟦ Syntax.ids∘s γ i ⟧subst = ⟦ γ ⟧subst 
-- ⟦ Syntax.∘s∘s γ γ' γ'' i ⟧subst = ⟦ γ'' ⟧subst ∘g ⟦ γ' ⟧subst ∘g ⟦ γ ⟧subst

-- -- ⟦ Syntax.var {A = A} ⟧tm-π i w p = ? -- Syntax.var-tys (⟦ A ⟧ty-π w p) (~ i)
-- -- ⟦ M Syntax.[ γ ] ⟧tm-π =
-- --   (λ i → ⟦ M ⟧tm-π i ∘g ⟦ γ ⟧subst)
-- --   ∙ (λ i → close-tm M ∘g ⟦ γ ⟧subst-π i)
-- --   ∙ funExt λ w → funExt λ p → Syntax.subst-∘ M γ (⟦ _ ⟧ctx-π w p)
-- -- ⟦ Syntax.⟨⟩ ⟧tm-π = ε-ind _ _ (ε-β _
-- --   ∙ sym (Syntax.subst-id _)
-- --   ∙ λ i → Syntax.⟨⟩ Syntax.[ ε-β {g = ClosedSubst Syntax.εc} Syntax.ids (~ i) ])
-- -- ⟦ Syntax.ε-L M ⟧tm-π =
-- --   (λ i → ⟦ M ⟧tm-π i ∘g id ,⊗ ⊗-unit-l⁻)
-- --   ∙ {!λ i → ⟦ M ⟧tm' ∘g !}
-- -- ⟦ M₁ Syntax.,⊗ M₂ ⟧tm-π =
-- --   (λ i → lax-ty _ _ ∘g ⟦ M₁ ⟧tm-π i ,⊗ ⟦ M₂ ⟧tm-π i)
-- --   ∙ ? -- ∙ λ i → lax-ty-naturality M₁ M₂ i ∘g ⟦ _ ⟧ctx-π ,⊗ ⟦ _ ⟧ctx-π
-- -- ⟦ Syntax.⊗-L M ⟧tm-π = {!!}
-- -- ⟦ Syntax.inl ⟧tm-π = {!!}
-- -- ⟦ Syntax.inr ⟧tm-π = {!!}
-- -- ⟦ Syntax.nil ⟧tm-π = {!!}
-- -- ⟦ Syntax.cons ⟧tm-π = {!!}
-- -- -- fillers once we have the grammars are sets
-- -- ⟦ Syntax.subst-id M i ⟧tm-π = {!!}

-- -- ⟦ Syntax.ids {Γ} ⟧subst-π i w p = Syntax.ids∘s (⟦ Γ ⟧ctx-π w p) (~ i)
-- -- ⟦ Syntax._∘s_ {Γ}{Γ'}{Γ''} γ' γ ⟧subst-π = funExt λ w → funExt λ p →
-- --   funExt⁻ (funExt⁻ ⟦ γ' ⟧subst-π w) _
-- --   ∙ (λ i → γ' Syntax.∘s ⟦ γ ⟧subst-π i w p)
-- --   ∙ λ i → Syntax.∘s∘s (⟦ Γ ⟧ctx-π w p) γ γ' (~ i)
-- -- ⟦ γ₁ Syntax.,⊗s γ₂ ⟧subst-π = {!!}
-- -- ⟦ Syntax.tys M ⟧subst-π = {!!}
-- -- -- These are trivial fillers, follow if all grammars are sets (they are)
-- -- ⟦ Syntax.ids∘s γ i ⟧subst-π = {!!}
-- -- ⟦ Syntax.∘s∘s γ γ' γ'' i ⟧subst-π = {!!}


-- -- ⟦string⟧ : ∀ w → ⟦ Syntax.⌈ w ⌉ ⟧ctx w
-- -- ⟦string⟧ = List.elim
-- --   ε-intro
-- --   λ {c}{w} ⟦⌈w⌉⟧ → ⊗-intro' [ c ] w literal-intro ⟦⌈w⌉⟧ 
-- -- ⟦string⟧-id : ∀ w → ⟦ Syntax.⌈ w ⌉ ⟧ctx-π w (⟦string⟧ w) ≡ Syntax.ids
-- -- ⟦string⟧-id = List.elim
-- --   (ε-β {g = ClosedSubst (Syntax.⌈ [] ⌉)} Syntax.ids)
-- --   -- (ε-β {g = {!!}} Syntax.ids)
-- --   λ {c}{w'} ⟦string⟧⟨w'⟩≡ids → {!!}
-- --   -- ((JRefl {x = []} (λ w _ → ⟦ Syntax.εc ⟧ctx' w) _))
-- --   -- λ {c}{w'} ⟦string⟧⟨w'⟩≡ids → {!!}

-- -- -- these are the "canonicalization" functions: they take in terms of type ⌈ w ⌉ ⊢ M : A and output ⟦ A ⟧ty w
-- -- ⟦_⟧ty-π⁻ : ∀ (A : Syntax.Ty) → ClosedTm A ⊢ ⟦ A ⟧ty
-- -- ⟦_⟧ctx-π⁻ : ∀ (Γ : Syntax.Ctx) → ClosedSubst Γ ⊢ ⟦ Γ ⟧ctx

-- -- ⟦ A ⟧ty-π⁻ w M = ⟦ M ⟧tm w (⟦string⟧ w)
-- -- ⟦ Γ ⟧ctx-π⁻ w γ = ⟦ γ ⟧subst w (⟦string⟧ w)

-- -- tm-canonicity : ∀ A → StrongEquivalence ⟦ A ⟧ty ClosedTm A
-- -- tm-canonicity A = mkStrEq ⟦ A ⟧ty-π ⟦ A ⟧ty-π⁻
-- --   (funExt (λ w → funExt λ M →
-- --     (λ i → ⟦ M ⟧tm-π i w (⟦string⟧ w))
-- --     ∙ (λ i → M Syntax.[ ⟦string⟧-id w i ])
-- --     ∙ Syntax.subst-id M))
-- --   (funExt λ w → funExt λ p → {!!}) -- this would require another proof by induction, methinks
