{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Cubical.Data.DecFin where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.Function.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool as Bool using (Bool)
open import Cubical.Data.Empty as ⊥ using (⊥ ; isProp⊥ ; uninhabEquiv)
open import Cubical.Data.List as List using (List ; [] ; _∷_)
import      Cubical.Data.List.FinData as FinList hiding (ℓ ; A ; B)
import      Cubical.Data.List.More as ListMore
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More'
open import Cubical.Data.Unit

import      Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' : Level
    A A' : Type ℓ
    B : A → Type ℓ'

it : {T : Type ℓ} → {{T}} → T
it {{x}} = x

open import Cubical.Data.FinData as Fin public
  using (Fin ; zero ; suc ; FinVec)
open import Cubical.Data.FinData.More

FinOrdOn : Type ℓ → Type ℓ
FinOrdOn A = Σ[ n ∈ ℕ ] A ≃ Fin n

isFinSet : Type ℓ → Type ℓ
isFinSet A = Σ[ n ∈ ℕ ] PT.∥ A ≃ Fin n ∥₁

open import Cubical.Relation.Nullary as Dec public
  using (¬_ ; Dec ; yes ; no)


module _ where
  isDecProp : Type ℓ → Type ℓ
  isDecProp A = Dec A × isProp A

  import Cubical.Relation.Nullary.DecidablePropositions as DP

  StdlibDecProp→isDecProp : (P : DP.DecProp ℓ) → isDecProp (P .fst .fst)
  StdlibDecProp→isDecProp P = P .snd , P .fst .snd

  stdlibIsDecProp→isDecProp : {P : Type ℓ} → DP.isDecProp P → isDecProp P
  stdlibIsDecProp→isDecProp (Bool.false , e) = no (equivFun e) , isOfHLevelRespectEquiv 1 (invEquiv e) isProp⊥
  stdlibIsDecProp→isDecProp (Bool.true , e) = yes (invEq e tt) , isOfHLevelRespectEquiv 1 (invEquiv e) isPropUnit


-- FinOrdOn
FinOrdOnRespectEquiv : {A : Type ℓ} {B : Type ℓ'} → A ≃ B → FinOrdOn A → FinOrdOn B
FinOrdOnRespectEquiv A≃B (n , e) = n , invEquiv A≃B ∙ₑ e

FinOrdOnFin : {n : ℕ} → FinOrdOn (Fin n)
FinOrdOnFin = _ , idEquiv _

FinOrdOn⊥ : FinOrdOn ⊥
FinOrdOn⊥ = 0 , uninhabEquiv (idfun ⊥) Fin.¬Fin0

FinOrdOnUnit : FinOrdOn Unit
FinOrdOnUnit = 1 , invEquiv (isContr→≃Unit Fin.isContrFin1)

FinOrdOnΣ : FinOrdOn A → ((a : A) → FinOrdOn (B a)) → FinOrdOn (Σ A B)
FinOrdOnΣ {A = A} {B = B} (nA , eA) f =
  FinOrdOnRespectEquiv (invEquiv ΣAB≃ΣFinFin) (_ , FinΣ≃ nA nB)
  where
  nB = fst ∘ f ∘ invEq eA
  eB = λ a → f a .snd ∙ₑ pathToEquiv (congS (Fin ∘ fst ∘ f) (sym (retEq eA a)))
  ΣAB≃ΣFinFin = Σ-cong-equiv eA eB


-- isFinSet
isPropIsFinSet : {A : Type ℓ} → isProp (isFinSet A)
isPropIsFinSet p q =
  Σ≡Prop (λ _ → PT.isPropPropTrunc)
    (PT.elim2 (λ _ _ → isSetℕ _ _)
    (λ A≃Finp A≃Finq → injFin (ua (invEquiv A≃Finp ∙ₑ A≃Finq)))
    (p .snd) (q .snd))

FinOrdOn→isFinSet : {A : Type ℓ} → FinOrdOn A → isFinSet A
FinOrdOn→isFinSet (n , e) = n , PT.∣ e ∣₁

isFinSet→∥FinOrdOn∥ : {A : Type ℓ} → isFinSet A → PT.∥ FinOrdOn A ∥₁
isFinSet→∥FinOrdOn∥ (n , ∣e∣) = PT.rec PT.isPropPropTrunc (λ e → PT.∣ n , e ∣₁) ∣e∣

isFinSetΣ : {A : Type ℓ} {B : A → Type ℓ'} → isFinSet A → (∀ a → isFinSet (B a)) → isFinSet (Σ A B)
isFinSetΣ {B = B} isFinSetA isFinSetB =
  isFinSet→∥FinOrdOn∥ isFinSetA
  |> PT.rec isPropIsFinSet
    (λ FinOrdOnA → (isFinSet→∥FinOrdOn∥ ∘ isFinSetB ∘ invEq (FinOrdOnA .snd))
    |> PT.recFin isPropIsFinSet
      (λ FinOrdOnB → FinOrdOnΣ FinOrdOnA
        (subst (FinOrdOn ∘ B) (retIsEq (FinOrdOnA .snd .snd) _) ∘ FinOrdOnB ∘ equivFun (FinOrdOnA .snd))
        |> FinOrdOn→isFinSet))

-- isFinSet→isSet : {A : Type ℓ} → isFinSet A → isSet A
-- isFinSet→isSet isFinSetA = {!!}


-- Dec
instance
  Dec∥∥ : {A : Type ℓ} → {{Dec A}} → Dec PT.∥ A ∥₁
  Dec∥∥ {{dec}} = Dec.Dec∥∥ dec

  DecFin : {n : ℕ} → Dec (Fin n)
  DecFin {zero} = no Fin.¬Fin0
  DecFin {suc n} = yes zero

≃Fin→Dec : {A : Type ℓ} {n : ℕ} → A ≃ Fin n → Dec A
≃Fin→Dec e = Dec.EquivPresDec (invEquiv e) DecFin

instance
  FinOrdOn→Dec : {A : Type ℓ} → {{FinOrdOn A}} → Dec A
  FinOrdOn→Dec {{n , e}} = ≃Fin→Dec e

  isFinSet→Dec∥∥ : {A : Type ℓ} → {{isFinSet A}} → Dec PT.∥ A ∥₁
  isFinSet→Dec∥∥ {{n , ∣e∣}} = ∣e∣ |> PT.rec (Dec.isPropDec PT.isPropPropTrunc) (Dec.Dec∥∥ ∘ ≃Fin→Dec)


-- isDecProp
instance
  isDecProp→Dec : {A : Type ℓ} → {{isDecProp A}} → Dec A
  isDecProp→Dec {{dec , _}} = dec

  isDecProp→FinOrdOn : {A : Type ℓ} → {{isDecProp A}} → FinOrdOn A
  isDecProp→FinOrdOn {{yes a , prop}} = FinOrdOnRespectEquiv (invEquiv (isContr→≃Unit (a , prop a))) FinOrdOnUnit
  isDecProp→FinOrdOn {{no ¬A , prop}} = FinOrdOnRespectEquiv (uninhabEquiv (idfun ⊥) ¬A) FinOrdOn⊥


FinOrd : (ℓ : Level) → Type (ℓ-suc ℓ)
FinOrd ℓ = TypeWithStr ℓ FinOrdOn

FinSet : (ℓ : Level) → Type (ℓ-suc ℓ)
FinSet ℓ = TypeWithStr ℓ isFinSet

Decidable : (ℓ : Level) → Type (ℓ-suc ℓ)
Decidable ℓ = TypeWithStr ℓ Dec

DecProp : (ℓ : Level) → Type (ℓ-suc ℓ)
DecProp ℓ = TypeWithStr ℓ isDecProp


module FinDec where

  -- DecΣ : {n : ℕ} → (P : Fin n → Type ℓ) → {{∀ i → Dec (P i)}} → Dec (Σ[ i ∈ Fin n ] P i)
  -- DecΣ {n = zero} P = no λ (i , Pi) → Fin.¬Fin0 i
  -- DecΣ {n = suc n} P {{decP}} =
  --   DecΣ (P ∘ suc) {{decP ∘ suc}} |> Dec.decRec (λ (i , Pi) → yes (suc i , Pi)) λ ¬Psuc →
  --   decP zero |> Dec.decRec (yes ∘ (_ ,_)) λ ¬Pzero →
  --   let ¬P = λ { (zero , Pzero) → ¬Pzero Pzero
  --              ; (suc i , Psuci) → ¬Psuc (i , Psuci) } in
  --   no ¬P

  -- DecidableΣ : {n : ℕ} → (P : Fin n → Decidable ℓ) → Decidable ℓ
  -- DecidableΣ {n = n} P = (Σ[ i ∈ Fin n ] ⟨ P i ⟩) , DecΣ (fst ∘ P) {{snd ∘ P}}

-- -- DecProp
-- record isDecProp (A : Type ℓ) : Type ℓ where
--   field
--     hasIsProp : isProp A
--     hasDec : Dec A

--   hasBool : Bool
--   hasBool = Bool.Dec→Bool hasDec

--   has≃bool : A ≃ Bool.Bool→Type hasBool
--   has≃bool = Bool.Dec≃DecBool hasIsProp hasDec

-- DecProp : (ℓ : Level) → Type (ℓ-suc ℓ)
-- DecProp ℓ = TypeWithStr ℓ isDecProp

-- DecProp→Bool : DecProp ℓ → Bool
-- DecProp→Bool P = isDecProp.hasBool $ str P

-- DecProp→≃Bool : (P : DecProp ℓ) → ⟨ P ⟩ ≃ Bool.Bool→Type (DecProp→Bool P)
-- DecProp→≃Bool P = isDecProp.has≃bool $ str P


-- -- FinOrd
-- FinOrd : (ℓ : Level) → Type (ℓ-suc ℓ)
-- FinOrd ℓ = TypeWithStr _ isFinOrd

-- _FinOrd⟶_ : FinOrd ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
-- A FinOrd⟶ B = ⟨ A ⟩ → B

-- FinOrdℙ : FinOrd ℓ → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
-- FinOrdℙ A ℓ' = A FinOrd⟶ DecProp ℓ'

-- lookupFinOrd : (A : FinOrd ℓ) (i : Fin _) → ⟨ A ⟩
-- lookupFinOrd A = invEq $ str A .snd


-- -- FinSet
-- _FinSet⟶_ : FinSet ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
-- A FinSet⟶ B = ⟨ A ⟩ → B

-- FinSetℙ : FinSet ℓ → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
-- FinSetℙ A ℓ' = A FinSet⟶ DecProp ℓ'


-- lemma : (A : FinOrd ℓ) → (P : FinOrdℙ A ℓ') →
--   (Σ[ x ∈ ⟨ A ⟩ ] ⟨ P x ⟩)
--   ≃ (Σ[ i ∈ Fin _ ] (Bool.Bool→Type ∘ DecProp→Bool ∘ P) (lookupFinOrd A i))
-- lemma A P =
--   Σ-cong-equiv (str A .snd) (transpFamily $ str A)
--   ∙ₑ Σ-cong-equiv-snd (DecProp→≃Bool ∘ P ∘ invEq (str A .snd))
--   where open import Cubical.Data.Sigma


-- isDecΣ : (A : FinOrd ℓ) (B : A FinOrd⟶ DecProp ℓ') → Dec (Σ[ x ∈ ⟨ A ⟩ ] ⟨ B x ⟩)
-- isDecΣ (⟨A⟩ , ℕ.zero , e) B = Dec.no λ (x , Bx) → equivFun e x
-- isDecΣ (⟨A⟩ , ℕ.suc n , e) B = {!invEq e Fin.fzero!}

-- isDec∃ : (A : FinSet ℓ) (B : A FinSet⟶ DecProp ℓ') → Dec PT.∥ Σ ⟨ A ⟩ (fst ∘ B) ∥₁
-- isDec∃ A B = PT.rec {!PT.isPropPropTrunc!} {!!} (str A .snd)

-- isDecProp∃ : (A : FinSet ℓ) (B : A FinSet⟶ DecProp ℓ') → isDecProp PT.∥ Σ ⟨ A ⟩ (fst ∘ B) ∥₁
-- isDecProp∃ A B .isDecProp.hasIsProp = PT.isPropPropTrunc
-- isDecProp∃ A B .isDecProp.hasDec = isDec∃ A B

-- DecProp∃ : (A : FinSet ℓ) (B : A FinSet⟶ DecProp ℓ') → DecProp (ℓ-max ℓ ℓ')
-- DecProp∃ A B = PT.∥ Σ ⟨ A ⟩ (fst ∘ B) ∥₁ , isDecProp∃ A B


-- isFinOrdSub : (X : Type ℓ) → isFinOrd X → (P : X → DecProp ℓ') → isFinOrd (Σ X (⟨_⟩ ∘ P))
-- isFinOrdSub X isFinOrdX P = _ ,
--   lemma (X , isFinOrdX) P
--   ∙ₑ Fin.SumFinSub≃ _ (DecProp→Bool ∘ P ∘ invEq (isFinOrdX .snd))
--   where open import Cubical.Data.Sigma

-- FinOrdRestrict : (A : FinOrd ℓ) → FinOrdℙ A ℓ' → FinOrd (ℓ-max ℓ ℓ')
-- FinOrdRestrict A P = Σ ⟨ A ⟩ (fst ∘ P) , isFinOrdSub ⟨ A ⟩ (str A) P


-- isFinSetSub : (X : Type ℓ) → isFinSet X → (P : X → DecProp ℓ') → isFinSet (Σ X (⟨_⟩ ∘ P))
-- isFinSetSub X isFinSetX P = PT.rec isPropIsFinSet
--   (λ e → isFinOrd→isFinSet $ isFinOrdSub X (_ , e) P)
--   (isFinSetX .snd)

-- FinSetRestrict : (A : FinSet ℓ) → FinSetℙ A ℓ' → FinSet (ℓ-max ℓ ℓ')
-- FinSetRestrict A P = Σ ⟨ A ⟩ (fst ∘ P) , isFinSetSub ⟨ A ⟩ (str A) P

