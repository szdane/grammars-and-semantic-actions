module Cubical.Data.SumFin.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.SumFin
open import Cubical.Data.Nat
import      Cubical.Data.Nat.Order.Recursive as NatOrd

private
  variable
    n : ℕ

bounded : (a : Fin n) → toℕ a NatOrd.≤ n
bounded {n = suc n} fzero = tt
bounded {n = suc n} (fsuc a) = bounded a

_≤_ : Fin n → Fin n → Type _
a ≤ b = toℕ a NatOrd.≤ toℕ b

_<_ : Fin n → Fin n → Type _
a < b = toℕ a NatOrd.< toℕ b

≤-flast : (a : Fin (suc n)) → a ≤ flast {k = n}
≤-flast fzero = tt
≤-flast {n = suc n} (fsuc a) = ≤-flast a

sub≤ : (a b : Fin n) → b ≤ a → Fin (n ∸ toℕ b)
sub≤ {n = suc n} a fzero b≤a = a
sub≤ {n = suc n} (fsuc a) (fsuc b) b≤a = sub≤ a b b≤a

sub≤-suc : (a b : Fin (suc n)) → b ≤ a → Fin (suc (n ∸ toℕ b))
sub≤-suc a fzero b≤a = a
sub≤-suc {n = suc n} (fsuc a) (fsuc b) b≤a = sub≤-suc a b b≤a

sub≤-suc' : (a b : Fin (suc n)) → b ≤ a → Fin (suc n)
sub≤-suc' a fzero b≤a = a
sub≤-suc' {n = suc n} (fsuc a) (fsuc b) b≤a = finj $ sub≤-suc' a b b≤a

fplus : (k : ℕ) → Fin n → Fin (k + n)
fplus zero a = a
fplus (suc k) a = fsuc (fplus k a)

fincl : (k : ℕ) → Fin n → Fin (k + n)
fincl zero a = a
fincl (suc k) a = finj (fincl k a)

record Range (n : ℕ) : Type ℓ-zero where
  field
    i j : Fin (suc n)
    i≤j : i ≤ j

  j' : Fin (suc (n ∸ toℕ i))
  j' = sub≤-suc j i i≤j

  length : Fin (suc n)
  length = sub≤-suc' j i i≤j

  complementSize : Fin (suc n)
  complementSize = sub≤-suc' flast length (≤-flast length)
  -- toℕ i + (n ∸ toℕ i ∸ toℕ j')

  -- partition : length + complementSize ≡ n
  -- partition = {!!}

