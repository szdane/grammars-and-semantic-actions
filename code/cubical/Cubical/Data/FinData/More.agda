module Cubical.Data.FinData.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Function.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Fin as Finℕ using () renaming (Fin to Finℕ)
open import Cubical.Data.FinData
import      Cubical.Data.FinData.SucIso as FinSucIso
open import Cubical.Data.Nat as Nat using (ℕ ; _+_)
import      Cubical.Data.Nat.Order.Recursive as NatOrd
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More'
open import Cubical.Data.Sum as ⊎ hiding (elim)
import      Cubical.Data.Sum.More as ⊎More
open import Cubical.Data.SumFin as SumFin using () renaming (Fin to SumFin)
import      Cubical.Data.SumFin.More as SumFinMore
open import Cubical.Data.Unit

open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
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

Finsuc≡Unit⊎Fin : Fin (ℕ.suc n) ≡ Unit ⊎ Fin n
Finsuc≡Unit⊎Fin = Fin≡SumFin ∙ congS (Unit ⊎_) (sym Fin≡SumFin)

Finsuc≡→Fin≡ : Fin (ℕ.suc m) ≡ Fin (ℕ.suc n) → Fin m ≡ Fin n
Finsuc≡→Fin≡ p = FinSucIso.Suc≡ (sym Finsuc≡Unit⊎Fin ∙ p ∙ Finsuc≡Unit⊎Fin)

injFin : Fin m ≡ Fin n → m ≡ n
injFin {ℕ.zero} {ℕ.zero} p = refl
injFin {ℕ.zero} {ℕ.suc n} p = transport⁻ p zero |> ¬Fin0 |> ⊥.rec
injFin {ℕ.suc m} {ℕ.zero} = sym ∘ injFin ∘ sym
injFin {ℕ.suc m} {ℕ.suc n} p = congS ℕ.suc (injFin (Finsuc≡→Fin≡ p))

FinΣ≃ : (n : ℕ) (m : FinVec ℕ n) → Σ (Fin n) (Fin ∘ m) ≃ Fin (foldrFin _+_ 0 m)
FinΣ≃ n m =
  Σ-cong-equiv Fin≃SumFin (λ fn → ≡→Fin≃SumFin (congS m (sym (retIsEq (Fin≃SumFin .snd) fn))))
  ∙ₑ SumFin.SumFinΣ≃ n (m ∘ SumFin→Fin)
  ∙ₑ invEquiv (≡→Fin≃SumFin (sum≡ n m))
  where
  sum≡ : (n : ℕ) (m : FinVec ℕ n) → foldrFin _+_ 0 m ≡ SumFin.totalSum (m ∘ SumFin→Fin)
  sum≡ = Nat.elim (λ _ → refl) λ n x m → congS (m zero +_) (x (m ∘ suc))

DecΣ : (n : ℕ) → (P : FinVec (Type ℓ) n) → (∀ k → Dec (P k)) → Dec (Σ (Fin n) P)
DecΣ n P decP = EquivPresDec
  (Σ-cong-equiv-fst (invEquiv Fin≃SumFin))
  (SumFinMore.DecΣ n (P ∘ SumFin→Fin) (decP ∘ SumFin→Fin))

