module Cubical.Data.SumFin.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Function.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

import      Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ hiding (elim)
open import Cubical.Data.SumFin hiding (elim)
open import Cubical.Data.Nat as Nat hiding (elim)
import      Cubical.Data.Nat.Order.Recursive as NatOrd
import      Cubical.Data.Nat.Order as NatOrdDiff

open import Cubical.Relation.Nullary

private
  variable
    ℓ : Level
    m n : ℕ

DecΣ : (n : ℕ) → (P : Fin n → Type ℓ) → ((k : Fin n) → Dec (P k)) → Dec (Σ (Fin n) P)
DecΣ = Nat.elim
  (λ _ _ → no fst)
  (λ n ih P decP → decP fzero |> decRec
    (yes ∘ (_ ,_))
    (λ ¬Pzero → ih (P ∘ fsuc) (decP ∘ fsuc) |> mapDec
      (λ (k , Pk) → (fsuc k , Pk))
      (λ ¬Psuc →
        λ { (fzero , Pzero) → ¬Pzero Pzero
          ; (fsuc k , Pk) → ¬Psuc (k , Pk)
          })))

bounded : (a : Fin n) → toℕ a NatOrd.≤ n
bounded {n = suc n} fzero = tt
bounded {n = suc n} (fsuc a) = bounded a

_≤_ : Fin n → Fin n → Type _
a ≤ b = toℕ a NatOrd.≤ toℕ b

_<_ : Fin n → Fin n → Type _
a < b = toℕ a NatOrd.< toℕ b

≤-isProp : {i j : Fin n} → isProp (i ≤ j)
≤-isProp {i = i} {j} = NatOrd.isProp≤ {toℕ i} {toℕ j}

≤-refl : (i : Fin n) → i ≤ i
≤-refl = NatOrd.≤-refl ∘ toℕ

finj-≤-finj : {i j : Fin n} → i ≤ j → finj i ≤ finj j
finj-≤-finj {suc n} {fzero} {j} i≤j = tt
finj-≤-finj {suc n} {fsuc i} {fsuc j} i≤j = finj-≤-finj {n} {i} {j} i≤j

isMonotone : (Fin m → Fin n) → Type _
isMonotone f = ∀ {i j} → i ≤ j → f i ≤ f j

isPropIsMonotone : (f : Fin m → Fin n) → isProp (isMonotone f)
isPropIsMonotone f = isPropImplicitΠ2 λ i j → isProp→ (≤-isProp {i = f i} {f j})

isMonotoneId : isMonotone (idfun (Fin n))
isMonotoneId i≤j = i≤j

Monotone : (m n : ℕ) → Type _
Monotone m n = Σ[ f ∈ (Fin m → Fin n) ] isMonotone f

isSetMonotone : isSet (Monotone m n)
isSetMonotone = isSetΣ (isSet→ isSetFin) (isProp→isSet ∘ isPropIsMonotone)

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

