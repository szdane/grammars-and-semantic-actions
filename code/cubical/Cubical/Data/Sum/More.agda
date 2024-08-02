module Cubical.Data.Sum.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sum

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    A B : Type ℓ

¬inl≡inr : {a : A} {b : B} → ¬ inl a ≡ inr b
¬inl≡inr = lower ∘ ⊎Path.encode _ _

isInj-inl : {a a' : A} → inl {B = B} a ≡ inl a' → a ≡ a'
isInj-inl = isEmbedding→Inj isEmbedding-inl _ _

isInj-inr : {b b' : B} → inr {A = A} b ≡ inr b' → b ≡ b'
isInj-inr = isEmbedding→Inj isEmbedding-inr _ _

