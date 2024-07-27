module Cubical.Data.SimplicialSet.Induced where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Simplex
open import Cubical.Categories.Presheaf

open import Cubical.Data.Nat
open import Cubical.Data.SimplicialSet.Base
open import Cubical.Data.SumFin
open import Cubical.Data.SumFin.More

open import Cubical.Functions.Image
open import Cubical.Functions.Image.More

import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' : Level

module _
  (X : SimplicialSet ℓ)
  {T : Type ℓ'}
  (ϕ : SimplicialSet.Point X → T)
  (isSetT : isSet T)
  where

  open Functor
  private module X = SimplicialSet X

  private
    -- Since f determines the images of all points, we know what the point
    -- vector of the image of any simplex must be.
    points : {n : ℕ} → X.Simplex n → Fin n → T
    points x = ϕ ∘ X.points x

    -- We choose to use this to define the induced simplex sets, identifying in
    -- the image simplices with the same induced point vector.
    Simplex : ℕ → Type (ℓ-max ℓ ℓ')
    Simplex n = Image (points {n})

    isSetSimplex : {n : ℕ} → isSet (Simplex n)
    isSetSimplex = isSetImage (isSet→ isSetT)

    liftMap' : {m n : ℕ} → Monotone n m → X.Simplex m → Fin n → T
    liftMap' f = points ∘ X .F-hom f

    ϕ-points-map : {m n : ℕ} (x x' : X.Simplex m) → (∀ i → points x i ≡ points x' i) →
      (f : Monotone n m) → (∀ i → liftMap' f x i ≡ liftMap' f x' i)
    ϕ-points-map {m} {n} x x' pts f i = {!!}

    liftMap'' : {m n : ℕ} → Monotone n m → Simplex m → Fin n → T
    liftMap'' {n = suc n} f (ϕx , isInImϕx) = PT.rec→Set (isSet→ isSetT)
      (liftMap' f ∘ fst)
      (λ (x , ptsX) (x' , ptsX') → funExt λ i → {!!})
      isInImϕx

    liftMap : {m n : ℕ} → Monotone n m → Simplex m → Simplex n
    liftMap f (ptsX , ∣x∣) =
      let ptsY = PT.rec→Set (isSet→ isSetT) (liftMap' f ∘ fst) (λ (_ , px) (_ , py) → {!!}) ∣x∣ in
      ptsY , {!!}

  induced : SimplicialSet (ℓ-max ℓ ℓ')
  induced .F-ob n = Simplex n , isSetSimplex
  induced .F-hom = liftMap
  induced .F-id = {!!}
  induced .F-seq = {!!}

