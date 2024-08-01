module Cubical.Data.Sum.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A B : Type ℓ

¬inl≡inr : {a : A} {b : B} → ¬ inl a ≡ inr b
¬inl≡inr = lower ∘ ⊎Path.encode _ _

