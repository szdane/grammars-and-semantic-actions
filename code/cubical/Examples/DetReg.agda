module Examples.DetReg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_ ;_or_)
open import Cubical.Data.Nat as Nat
open import Cubical.Data.List hiding (init; rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum hiding (rec)
open import Cubical.Data.FinSet

private
  variable
    ℓg : Level

data Bracket : Type where
  [ ] : Bracket

BracketRep : Bracket ≃ Bool
BracketRep = isoToEquiv (iso
  (λ { [ → true ; ] → false })
  (λ { false → ] ; true → [ })
  (λ { false → refl ; true → refl })
  λ { [ → refl ; ] → refl })

isFinBracket : isFinSet Bracket
isFinBracket = EquivPresIsFinSet (invEquiv BracketRep) isFinSetBool

Alphabet : hSet _
Alphabet = (Bracket , isFinSet→isSet isFinBracket)

open import Grammar Alphabet
open import Grammar.RegularExpression Alphabet
open import Grammar.Maybe Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet

unambiguousDetReg :
  (r : DeterministicRegularExpression) →
 unambiguous (DeterministicRegularExpression→Grammar r)
unambiguousDetReg ε-DetReg = unambiguousε
unambiguousDetReg ⊥-DetReg = unambiguous⊥
unambiguousDetReg (literalDetReg c) = unambiguous-literal c
unambiguousDetReg ((A ⊕DetReg B) firsts-disjoint) = unambig
  where
  opaque
    unfolding _⊕_ ⊥ _&_
    unambig :
      unambiguous
      ((DeterministicRegularExpression→Grammar A) ⊕
        (DeterministicRegularExpression→Grammar B))
    unambig = unambiguous'→unambiguous
      λ { [] → {!!}
        ; (x ∷ w) →
        isProp⊎
          (unambiguous→unambiguous' isFinBracket
            {g = DeterministicRegularExpression→Grammar A}
            (unambiguousDetReg A) _)
          (unambiguous→unambiguous' isFinBracket
            {g = DeterministicRegularExpression→Grammar B}
            (unambiguousDetReg B) _)
          λ pa pb → firsts-disjoint (x ∷ []) ((get-first x w pa) , get-first x w pb)
        }
unambiguousDetReg ((A ⊗DetReg B) x x₁) = {!!}
unambiguousDetReg (non-null A) = {!!}
unambiguousDetReg (KL*DetReg A x) = {!!}

r : DeterministicRegularExpression
r =
  KL*DetReg
    ((literalDetReg [ ⊗DetReg literalDetReg ])
      (literal¬nullable [)
      {!!})
    {!!}
