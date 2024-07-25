module Cubical.Data.Vec.Between where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
open import Cubical.Data.Vec

private
  variable
    ℓ ℓ' : Level

data Between {T : Type ℓ} (R : T → T → Type ℓ') : {n : ℕ} → Vec T n → Type (ℓ-max ℓ ℓ') where
  [] : Between R []
  [_] : (x : T) → Between R (x ∷ [])
  [_]∶_∶ : (x : T) {hd : T} → R x hd → {n : ℕ} {xs : Vec T (1 + n)} → R x hd → hd ≡ head xs → Between R xs → Between R (x ∷ xs)

