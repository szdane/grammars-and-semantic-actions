module Cubical.Data.Sigma.More' where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level
    A A' : Type ℓ
    B : A → Type ℓ'

open Iso

Σ-cong-iso' : (isom : Iso A A') → Iso (Σ A B) (Σ A' (B ∘ isom .inv))
Σ-cong-iso' {B = B} isom =
  Σ-cong-iso {B' = B ∘ isom .inv} isom
    λ a → pathToIso (congS B (sym (isom .leftInv a)))

Σ-cong-equiv' : (e : A ≃ A') → Σ A B ≃ Σ A' (B ∘ invEq e)
Σ-cong-equiv' {B = B} e =
  Σ-cong-equiv {B' = B ∘ invEq e} e
    λ a → pathToEquiv (congS B (sym (retIsEq (e .snd) a)))

