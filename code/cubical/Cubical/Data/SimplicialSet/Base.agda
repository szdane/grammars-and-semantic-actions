module Cubical.Data.SimplicialSet.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Simplex
open import Cubical.Categories.Instances.SimplicialSet
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Yoneda

open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Data.SumFin.More

private
  variable
    ℓ : Level

SimplicialSet : (ℓ : Level) → Type (ℓ-suc ℓ)
SimplicialSet ℓ = SimplicialSetCat ℓ .Category.ob

-- standard n-simplex
Δ : ℕ → SimplicialSet ℓ-zero
Δ = yo


module SimplicialSet (X : SimplicialSet ℓ) where
  open Functor

  -- The collections of n-simplices
  Simplex : ℕ → Type ℓ
  Simplex n = X .F-ob n .fst

  isSetSimplex : (n : ℕ) → isSet (Simplex n)
  isSetSimplex n = X .F-ob n .snd

  -- Face map
  face : {n : ℕ} → Fin (suc n) → Simplex (suc n) → Simplex n
  face i = X .F-hom (ΔCat.δ i)

  -- The collection of points, i.e. 1-simplices
  Point : Type ℓ
  Point = Simplex 1

  -- The points on a simplex. For a point, this is the identity. For an edge,
  -- this is the boundary.
  points : {n : ℕ} → Simplex n → Fin n → Point
  points {1}           x fzero    = x
  points {suc (suc n)} x fzero    = points (face flast x) fzero
  points {suc (suc n)} x (fsuc i) = points (face fzero x) i

  points-map : {m n : ℕ} → (f : Monotone n m) → 

