module Cubical.Data.SimplexVec where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Vec
open import Cubical.Data.SumFin

private
  variable
    ℓ : Level

module _
  (S : (height : ℕ) → Type ℓ)
  (face : (height : ℕ) → Fin (suc height) → S (suc height) → S height)
  where

  -- A level is the data at a dimension. It is a vector of data drawn from (S n)
  -- for some n.
  --
  -- A level at a lower height is "simpler" data. For instance, level 0 is
  -- trivial, level 1 is points, level 2 is edges between points...
  --
  -- A level at a lower depth is "closer" to the "most complex" data. For
  -- instance, depth 0 is the highest level, depth 1 is just below that...

  private
    LevelData : ℕ → ℕ → Type _
    LevelData height depth = Vec (S height) (suc depth)

    DataWithSize : ℕ → Type _
    DataWithSize size = {!(height : Fin size) → !}

  SimplexVecLevel : ℕ → ℕ → Type _
  SimplexVecLevel zero depth = S zero
  SimplexVecLevel height@(suc height-1) depth = Σ[ xs ∈ Vec (S height) (suc depth) ] {!!}
