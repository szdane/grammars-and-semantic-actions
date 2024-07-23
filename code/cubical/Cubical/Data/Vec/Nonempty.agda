{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Cubical.Data.Vec.Nonempty where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin as SumFin hiding (elim)

private
  variable
    ℓ : Level
    T : Type ℓ
    n m : ℕ

data Vec⁺ (T : Type ℓ) : ℕ → Type ℓ where
  [_] : T → Vec⁺ T 0
  _∷_ : {n : ℕ} → T → Vec⁺ T n → Vec⁺ T (suc n)
infixr 5 _∷_

elim : {B : ∀ n → Vec⁺ T n → Type ℓ} →
       (∀ x → B 0 [ x ]) →
       (∀ n x (xs : Vec⁺ T n) → B n xs → B (suc n) (x ∷ xs)) →
       ∀ {n} (xs : Vec⁺ T n) → B n xs
elim base induct [ x ] = base x
elim base induct (x ∷ xs) = induct _ x xs (elim base induct xs)

ifoldr : ∀ {n} {U : ℕ → Type ℓ} → ((i : ℕ) → T → U i → U (suc i)) → U 0 → Vec⁺ T n → U n
ifoldr f acc [ x ] = acc
ifoldr f acc (x ∷ xs) = f _ x (ifoldr f acc xs)

pure : T → Vec⁺ T 0
pure x = [ x ]

head : Vec⁺ T n → T
head [ x ] = x
head (x ∷ xs) = x
{-# INJECTIVE_FOR_INFERENCE head #-}

last : Vec⁺ T n → T
last [ x ] = x
last (x ∷ xs) = last xs

lookup : Vec⁺ T n → Fin (suc n) → T
lookup xs fzero = head xs
lookup (x ∷ xs) (fsuc idx) = lookup xs idx

tabulate : (Fin (suc n) → T) → Vec⁺ T n
tabulate {n = 0} f = [ f fzero ]
tabulate {n = suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

AreSpliceable : Vec⁺ T n → Vec⁺ T m → Type _
AreSpliceable xs ys = last xs ≡ head ys

record Spliceable (T : Type ℓ) (n m : ℕ) : Type ℓ where
  constructor mk-spliceable
  field
    l : Vec⁺ T n
    r : Vec⁺ T m
    are-spliceable : AreSpliceable l r

  spliced : Vec⁺ T (n + m)
  spliced = ifoldr {U = λ i → Vec⁺ T (i + m)} (λ i → _∷_) r l

open Spliceable public using (are-spliceable ; spliced)

_∷l_ : T → Spliceable T n m → Spliceable T (suc n) m
x ∷l sp = mk-spliceable (x ∷ l) r (sp .are-spliceable)
  where open Spliceable sp

-- splice-head : {xs : Vec⁺ T n} {ys : Vec⁺ T m}
--               (spliceable : AreSpliceable xs ys) →
--               head xs ≡ head (splice xs ys spliceable)
-- splice-head {xs = [ x ]} spliceable = spliceable
-- splice-head {xs = x ∷ xs} spliceable = refl

split : (n : ℕ) {m : ℕ} (xs : Vec⁺ T (n + m)) → Σ[ sp ∈ Spliceable T n m ] xs ≡ spliced sp
split 0 xs = mk-spliceable (pure $ head xs) xs refl , refl
split (suc n) (x ∷ xs) =
  let (sp , p) = split n xs in
  x ∷l sp , congS (x ∷_) p

split' : ∀ n {m} (xs : Vec⁺ T (n + m)) → Spliceable T n m
split' n xs = split n xs .fst

-- split'³ : (k l : ℕ) {m : ℕ} (xs : Vec⁺ T (k + l + m)) → Vec⁺ T k × Vec⁺ T l × Vec⁺ T m
-- split'³ k l xs = Σ-assoc-Iso .Iso.fun $ map-fst (split' k) (split' (k + l) xs)

-- simplify : (k l : ℕ) {m : ℕ} (xs : Vec⁺ T (k + l + m)) →
--            AreSpliceable (split'³ k l xs .fst) (split'³ k l xs .snd .snd) →
--            Vec⁺ T (k + m)
-- simplify k l xs spliceable =
--   let (ls , _ , rs) = split'³ k l xs in
--   splice ls rs spliceable

headTabulate≡ap0 : (f : Fin (suc n) → T) → head (tabulate f) ≡ f fzero
headTabulate≡ap0 {n = 0} f = refl
headTabulate≡ap0 {n = suc n} f = refl

lookup-tabulate : (f : Fin (suc n) → T) (k : Fin (suc n)) → lookup (tabulate f) k ≡ f k
lookup-tabulate f fzero = headTabulate≡ap0 f
lookup-tabulate {n = suc n} f (fsuc k) = lookup-tabulate (f ∘ fsuc) k

tabulate-lookup : (xs : Vec⁺ T n) → tabulate (lookup xs) ≡ xs
tabulate-lookup [ x ] = refl
tabulate-lookup (x ∷ xs) = congS (x ∷_) $ tabulate-lookup xs

-- head-split : (n : ℕ) {m : ℕ} (xs : Vec⁺ T (n + m)) → head xs ≡ head (split n xs .fst .fst)
-- head-split 0 xs = refl
-- head-split (suc n) (x ∷ xs) = refl

-- head≡headSplice : (xs : Vec⁺ T n) (ys : Vec⁺ T m) (spliceable : AreSpliceable xs ys) → head xs ≡ head (splice xs ys spliceable)
-- head≡headSplice [ x ] ys lastxs≡headys = lastxs≡headys
-- head≡headSplice (x ∷ xs) ys lastxs≡headys = refl

module _ where
  open Iso

  Iso-Vec⁺-Finsuc→ : Iso (Vec⁺ T n) (Fin (suc n) → T)
  Iso-Vec⁺-Finsuc→ .fun = lookup
  Iso-Vec⁺-Finsuc→ .inv = tabulate
  Iso-Vec⁺-Finsuc→ .rightInv f = funExt (lookup-tabulate f)
  Iso-Vec⁺-Finsuc→ .leftInv = tabulate-lookup

  Vec⁺≃Finsuc→ : Vec⁺ T n ≃ (Fin (suc n) → T)
  Vec⁺≃Finsuc→ = isoToEquiv Iso-Vec⁺-Finsuc→

module _ (T : FinSet ℓ) where
  isFinSetVec⁺ : isFinSet (Vec⁺ (T .fst) n)
  isFinSetVec⁺ = EquivPresIsFinSet (invEquiv Vec⁺≃Finsuc→) (isFinSet→ (_ , isFinSetFin) T)

