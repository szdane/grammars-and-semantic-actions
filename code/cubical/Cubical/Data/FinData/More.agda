module Cubical.Data.FinData.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Function.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

import      Cubical.Data.Empty as ⊥
open import Cubical.Data.FinData
open import Cubical.Data.Nat as Nat using (ℕ ; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More'
open import Cubical.Data.Sum hiding (elim)
open import Cubical.Data.SumFin as SumFin using () renaming (Fin to SumFin)

private
  variable
    m n : ℕ

Fin→SumFin : Fin n → SumFin.Fin n
Fin→SumFin = elim (λ {n} _ → SumFin.Fin n) SumFin.fzero SumFin.fsuc

SumFin→Fin : SumFin.Fin n → Fin n
SumFin→Fin = SumFin.elim (λ {n} _ → Fin n) zero suc

FinSumFinIso : Iso (Fin n) (SumFin n)
FinSumFinIso = iso Fin→SumFin SumFin→Fin
  (SumFin.elim (λ fn → Fin→SumFin (SumFin→Fin fn) ≡ fn) refl (cong SumFin.fsuc))
  (elim (λ fn → SumFin→Fin (Fin→SumFin fn) ≡ fn) refl (cong suc))

≡→FinSumFinIso : m ≡ n → Iso (Fin m) (SumFin n)
≡→FinSumFinIso {m} = J (λ n p → Iso (Fin m) (SumFin n)) FinSumFinIso

Fin≃SumFin : Fin n ≃ SumFin n
Fin≃SumFin = isoToEquiv FinSumFinIso

≡→Fin≃SumFin : m ≡ n → Fin m ≃ SumFin n
≡→Fin≃SumFin {m} = J (λ n p → Fin m ≃ SumFin n) Fin≃SumFin

Fin≡SumFin : Fin n ≡ SumFin n
Fin≡SumFin = ua Fin≃SumFin

FinΣ≃ : (n : ℕ) (m : FinVec ℕ n) → Σ (Fin n) (Fin ∘ m) ≃ Fin (foldrFin _+_ 0 m)
FinΣ≃ n m =
  Σ-cong-equiv Fin≃SumFin (λ fn → ≡→Fin≃SumFin (congS m (sym (retIsEq (Fin≃SumFin .snd) fn))))
  ∙ₑ SumFin.SumFinΣ≃ n (m ∘ SumFin→Fin)
  ∙ₑ invEquiv (≡→Fin≃SumFin (sum≡ n m))
  where
  sum≡ : (n : ℕ) (m : FinVec ℕ n) → foldrFin _+_ 0 m ≡ SumFin.totalSum (m ∘ SumFin→Fin)
  sum≡ = Nat.elim (λ _ → refl) λ n x m → congS (m zero +_) (x (m ∘ suc))

module FinSigmaChar where


  Equiv : (n : ℕ) (m : FinVec ℕ n) → Σ (Fin n) (Fin ∘ m) ≃ Fin (foldrFin _+_ 0 m)
  Equiv ℕ.zero m .fst ()
  Equiv ℕ.zero m .snd .equiv-proof ()
  Equiv (ℕ.suc n) m =
    Σ-cong-equiv' (invEquiv (FinSumChar.Equiv 1 n))
    ∙ₑ Σ⊎≃
    ∙ₑ ⊎-equiv (Σ-contractFst isContrFin1) (Equiv n (m ∘ suc))
    ∙ₑ FinSumChar.Equiv _ _

inj-Fin : {m n : ℕ} → Fin m ≡ Fin n → m ≡ n
inj-Fin {ℕ.zero} {ℕ.zero} Finm≡Finn = refl
inj-Fin {ℕ.zero} {ℕ.suc n} Finm≡Finn =
  transport (sym Finm≡Finn) zero
  |> ¬Fin0
  |> ⊥.rec
inj-Fin {ℕ.suc m} {ℕ.zero} Finm≡Finn = sym $ inj-Fin (sym Finm≡Finn)
inj-Fin {ℕ.suc m} {ℕ.suc n} Finm≡Finn = congS ℕ.suc $ inj-Fin {m} {n}
  ({!⊎-equiv !} ∙ ua (FinSumChar.Equiv 1 m) ∙ {!!})

