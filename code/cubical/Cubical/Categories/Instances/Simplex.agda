module Cubical.Categories.Instances.Simplex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin
open import Cubical.Data.SumFin.More

module _ where
  open Category hiding (_∘_)

  ΔCat : Category ℓ-zero ℓ-zero
  ΔCat .ob = ℕ
  ΔCat .Hom[_,_] m n = Σ[ f ∈ (Fin m → Fin n) ] isMonotone f
  ΔCat .id = idfun _ , λ i≤j → i≤j
  ΔCat ._⋆_ (f , isMonotoneF) (g , isMonotoneG) = g ∘ f , isMonotoneG ∘ isMonotoneF
  ΔCat .⋆IdL _ = Σ≡Prop isPropIsMonotone refl
  ΔCat .⋆IdR _ = Σ≡Prop isPropIsMonotone refl
  ΔCat .⋆Assoc _ _ _ = Σ≡Prop isPropIsMonotone refl
  ΔCat .isSetHom = isSetΣ (isSet→ (isSetSumFin _)) (isProp→isSet ∘ isPropIsMonotone)


module ΔCat where
  open Category ΔCat

  δ : {n : ℕ} → Fin (suc n) → Hom[ n , suc n ]
  δ i = δ' _ i , isMonotoneδ' _ i
    where
    δ' : (n : ℕ) → Fin (suc n) → Fin n → Fin (suc n)
    δ' n fzero = fsuc
    δ' (suc n) (fsuc i) fzero = fzero
    δ' (suc n) (fsuc i) (fsuc k) = finj $ δ' n i k

    isMonotoneδ' : ∀ n i → isMonotone (δ' n i)
    isMonotoneδ' n fzero {k} {l} k≤l = k≤l
    isMonotoneδ' (suc n) (fsuc i) {fzero} {l} k≤l = tt
    isMonotoneδ' (suc n) (fsuc i) {fsuc k} {fsuc l} k≤l =
      finj-≤-finj {suc n} {δ' n i k} {δ' n i l} (isMonotoneδ' n i k≤l)

