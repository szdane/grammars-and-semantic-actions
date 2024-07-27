module Cubical.Categories.Instances.NatOrd where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Poset

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive

open import Cubical.Relation.Binary.Order.Poset

open Category

private
  isPosetℕ : IsPoset _≤_
  isPosetℕ .IsPoset.is-set = isSetℕ
  isPosetℕ .IsPoset.is-prop-valued n m = isProp≤ {n} {m}
  isPosetℕ .IsPoset.is-refl = ≤-refl
  isPosetℕ .IsPoset.is-trans k m n = ≤-trans {k} {m} {n}
  isPosetℕ .IsPoset.is-antisym m n = ≤-antisym {m} {n}

  ℕPoset : Poset ℓ-zero ℓ-zero
  ℕPoset = poset _ _ isPosetℕ

NatOrdCat : Category ℓ-zero ℓ-zero
NatOrdCat = PosetCategory ℕPoset

