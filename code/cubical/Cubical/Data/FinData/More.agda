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

module _ where
  open Iso

  split : ∀ x → (x ≡ inl tt) ⊎ (Σ[ k ∈ Fin n ] x ≡ inr k)
  split (inl tt) = inl refl
  split (inr k) = inr (k , refl)

  module _
    (isom : Iso (Unit ⊎ Fin m) (Unit ⊎ Fin n))
    where

    disc : {k : ℕ} → Discrete (Unit ⊎ Fin k)
    disc = discrete⊎ (λ _ _ → yes refl) discreteFin

    fl : Unit → Unit ⊎ Fin n
    fl = isom .fun ∘ inl

    fr : Fin m → Unit ⊎ Fin n
    fr = isom .fun ∘ inr

    Unit↦Unit = fl tt ≡ inl tt

    Fin↦Fin : Fin m → Type _
    Fin↦Fin k = Σ[ k' ∈ Fin n ] (fr k ≡ inr k')
    ∀Fin↦Fin = (k : Fin m) → Fin↦Fin k

    Unit↦Unit→¬Fin↦Unit : (k : Fin m) → Unit↦Unit → ¬ fr k ≡ inl tt
    Unit↦Unit→¬Fin↦Unit k UU FU = isoFunInjective isom _ _ (UU ∙ sym FU) |> ⊎More.¬inl≡inr

    ¬Fin↦Unit→Fin↦Fin : (k : Fin m) → ¬ fr k ≡ inl tt → Fin↦Fin k
    ¬Fin↦Unit→Fin↦Fin k ¬F→U = split (fr k) |> ⊎.rec (⊥.elim ∘ ¬F→U) (idfun _)

    Unit↦Unit→∀Fin↦Fin : Unit↦Unit → ∀Fin↦Fin
    Unit↦Unit→∀Fin↦Fin UU k = Unit↦Unit→¬Fin↦Unit k UU |> ¬Fin↦Unit→Fin↦Fin k

    flip↦ : ∀ {x y} → isom .fun x ≡ y → isom .inv y ≡ x
    flip↦ x↦y = congS (isom .inv) (sym x↦y) ∙ isom .leftInv _

  module _
    (isom : Iso (Unit ⊎ Fin m) (Unit ⊎ Fin n))
    (UU : Unit↦Unit isom)
    where

    fun' : Fin m → Fin n
    fun' fm = Unit↦Unit→∀Fin↦Fin isom UU fm .fst

    inv' : Fin n → Fin m
    inv' fn = Unit↦Unit→∀Fin↦Fin (invIso isom) (flip↦ isom UU) fn .fst

    compute-fun' : ∀ k → isom .fun (inr k) ≡ inr (fun' k)
    compute-fun' k with split (isom .fun (inr k))
    ... | inl FU = Unit↦Unit→¬Fin↦Unit isom k UU FU |> ⊥.rec
    ... | inr FF = FF .snd

    compute-inv' : ∀ k → isom .inv (inr k) ≡ inr (inv' k)
    compute-inv' k with split (isom .inv (inr k))
    ... | inl FU = Unit↦Unit→¬Fin↦Unit (invIso isom) k (flip↦ isom UU) FU |> ⊥.rec
    ... | inr FF = FF .snd

    sec : section fun' inv'
    sec k =
      congS (isom .fun) (compute-inv' k) ∙ compute-fun' (inv' k)
      |> sym
      |> _∙ isom .rightInv (inr k)
      |> isEmbedding→Inj isEmbedding-inr _ _

    isom' : Iso (Fin m) (Fin n)
    isom' = iso fun' inv' sec {!!}

