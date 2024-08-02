module Cubical.Data.FinData.SucIso where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Function.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.FinData
open import Cubical.Data.Nat as Nat using (ℕ ; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ hiding (elim)
import      Cubical.Data.Sum.More as ⊎More
open import Cubical.Data.Unit

open import Cubical.Functions.Involution

open import Cubical.Relation.Nullary

private
  variable
    m n : ℕ

open Iso

split : ∀ x → (x ≡ inl tt) ⊎ (Σ[ k ∈ Fin n ] x ≡ inr k)
split (inl tt) = inl refl
split (inr k) = inr (k , refl)

UnitIso : ℕ → ℕ → Type _
UnitIso m n = Iso (Unit ⊎ Fin m) (Unit ⊎ Fin n)

module _
  (isom : UnitIso m n)
  where

  fl = isom .fun ∘ inl
  fr = isom .fun ∘ inr
  UU = fl tt ≡ inl tt
  FF = (k : Fin m) → Σ[ k' ∈ Fin n ] fr k ≡ inr k'

  module _ (uu : UU) where

    UU→¬FU : ∀ k → ¬ fr k ≡ inl tt
    UU→¬FU k fu = isoFunInjective isom _ _ (uu ∙ sym fu) |> ⊎More.¬inl≡inr

    UU→FF : FF
    UU→FF k = split (isom .fun (inr k)) |> ⊎.rec (⊥.rec ∘ UU→¬FU k) (idfun _)

    compute : ∀ k → fr k ≡ inr (UU→FF k .fst)
    compute k with split (fr k)
    ... | inr ff = ff .snd
    ... | inl fu = UU→¬FU k fu |> ⊥.rec

module _
  (isom : UnitIso m n)
  (uf : Σ[ k ∈ Fin n ] isom .fun (inl tt) ≡ inr k)
  where

  swap : Unit ⊎ Fin n → Unit ⊎ Fin n
  swap (inl tt) = inr (uf .fst)
  swap (inr k) = discreteFin k (uf .fst) |> decRec (λ _ → inl tt) (λ _ → inr k)

  discRefl : (k : Fin n) → discreteFin k k ≡ yes refl
  discRefl k with discreteFin k k
  ... | yes p = congS yes $ isSetFin _ _ p refl
  ... | no ¬p = ¬p refl |> ⊥.rec

  isInvolSwap : isInvolution swap
  isInvolSwap (inl tt) with discreteFin (uf .fst) (uf .fst)
  ... | yes p = refl
  ... | no ¬p = ¬p refl |> ⊥.rec
  isInvolSwap (inr k) with discreteFin k (uf .fst)
  ... | yes p = congS inr (sym p)
  ... | no ¬p with discreteFin k (uf .fst)
  ... |   yes p = ¬p p |> ⊥.rec
  ... |   no ¬q = refl

  swapIso = involIso {f = swap} isInvolSwap
  compSwap = compIso isom swapIso

  UUcompSwap : UU compSwap
  UUcompSwap =
    congS swap (uf .snd)
    ∙ congS (decRec (λ _ → inl tt) (λ _ → inr (uf .fst))) (discRefl (uf .fst))

module _ (isom : UnitIso m n) where

  flip↦ : ∀ {x y} → isom .fun x ≡ y → isom .inv y ≡ x
  flip↦ x↦y = congS (isom .inv) (sym x↦y) ∙ isom .leftInv _

  module _ (uu : UU isom) where

    fun' = fst ∘ UU→FF isom uu
    inv' = fst ∘ UU→FF (invIso isom) (flip↦ uu)
    compute-fun' = compute isom uu
    compute-inv' = compute (invIso isom) (flip↦ uu)

    sec : section fun' inv'
    sec k =
      congS (isom .fun) (compute-inv' k) ∙ compute-fun' (inv' k)
      |> sym
      |> _∙ isom .rightInv (inr k)
      |> ⊎More.isInj-inr

    ret : retract fun' inv'
    ret k =
      congS (isom .inv) (compute-fun' k) ∙ compute-inv' (fun' k)
      |> sym
      |> _∙ isom .leftInv (inr k)
      |> ⊎More.isInj-inr

    isom' : Iso (Fin m) (Fin n)
    isom' = iso fun' inv' sec ret

UUisom : UnitIso m n → Σ[ isom ∈ UnitIso m n ] UU isom
UUisom isom = split (isom .fun (inl tt)) |> ⊎.elim
  (λ uu → (isom , uu))
  (λ uf → (compSwap isom uf , UUcompSwap isom uf))

SucIso : UnitIso m n → Iso (Fin m) (Fin n)
SucIso isom = uncurry isom' (UUisom isom)

Suc≡ : Unit ⊎ Fin m ≡ Unit ⊎ Fin n → Fin m ≡ Fin n
Suc≡ = isoToPath ∘ SucIso ∘ pathToIso

