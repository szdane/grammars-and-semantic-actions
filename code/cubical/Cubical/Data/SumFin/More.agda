module Cubical.Data.SumFin.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.SumFin
open import Cubical.Data.Nat
import      Cubical.Data.Nat.Order.Recursive as NatOrd

private
  variable
    n : ℕ

_≤_ : Fin n → Fin n → Type _
a ≤ b = toℕ a NatOrd.≤ toℕ b

_<_ : Fin n → Fin n → Type _
a < b = toℕ a NatOrd.< toℕ b

≤-flast : (a : Fin (suc n)) → a ≤ flast {k = n}
≤-flast fzero = tt
≤-flast {n = suc n} (fsuc a) = ≤-flast a

sub≤ : (a b : Fin n) → b ≤ a → Fin n
sub≤ {n = suc n} a fzero b≤a = a
sub≤ {n = suc n} (fsuc a) (fsuc b) b≤a = finj $ sub≤ a b b≤a

fplus : (k : ℕ) → Fin n → Fin (k + n)
fplus zero a = a
fplus (suc k) a = fsuc (fplus k a)

