module Cubical.Data.List.More where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List

private
  variable
    ℓ : Level
    A B : Type ℓ

bind : List A → (A → List B) → List B
bind [] f = []
bind (x ∷ xs) f = f x ++ bind xs f

