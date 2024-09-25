open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.RegularExpression (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure

open import Helper
open import Grammar Alphabet

private
  variable ℓG ℓG' : Level


data RegularExpression  : Type ℓ-zero where
  ε-Reg : RegularExpression
  ⊥-Reg : RegularExpression
  _⊗Reg_ : RegularExpression →
    RegularExpression → RegularExpression
  literalReg : ⟨ Alphabet ⟩ → RegularExpression
  _⊕Reg_ : RegularExpression → RegularExpression → RegularExpression
  KL*Reg : RegularExpression → RegularExpression

RegularExpression→Grammar : RegularExpression → Grammar ℓ-zero
RegularExpression→Grammar  ε-Reg = ε
RegularExpression→Grammar  ⊥-Reg = ⊥
RegularExpression→Grammar (g ⊗Reg g') =
  (RegularExpression→Grammar g) ⊗ (RegularExpression→Grammar g')
RegularExpression→Grammar (literalReg c) = literal c
RegularExpression→Grammar (g ⊕Reg g') =
  RegularExpression→Grammar g ⊕ RegularExpression→Grammar g'
RegularExpression→Grammar (KL*Reg g) = KL* (RegularExpression→Grammar g)

data DeterministicRegularExpression : Type ℓ-zero
DeterministicRegularExpression→Grammar :
  DeterministicRegularExpression → Grammar ℓ-zero

data DeterministicRegularExpression where
  ε-DetReg : DeterministicRegularExpression
  ⊥-DetReg : DeterministicRegularExpression
  literalDetReg : ⟨ Alphabet ⟩ → DeterministicRegularExpression
  _⊕DetReg_ :
    (A B : DeterministicRegularExpression) →
    disjoint
      (first (DeterministicRegularExpression→Grammar A))
      (first (DeterministicRegularExpression→Grammar B)) →
    DeterministicRegularExpression
  _⊗DetReg_ :
    (A B : DeterministicRegularExpression) →
    ¬nullable (DeterministicRegularExpression→Grammar A) →
    disjoint
      (followlast (DeterministicRegularExpression→Grammar A))
      (first (DeterministicRegularExpression→Grammar B)) →
    DeterministicRegularExpression
  non-null_ : DeterministicRegularExpression → DeterministicRegularExpression
  KL*DetReg : (A : DeterministicRegularExpression) →
    disjoint
      (followlast (DeterministicRegularExpression→Grammar A))
      (first (DeterministicRegularExpression→Grammar A)) →
    DeterministicRegularExpression

DeterministicRegularExpression→Grammar ε-DetReg = ε
DeterministicRegularExpression→Grammar ⊥-DetReg = ⊥
DeterministicRegularExpression→Grammar (literalDetReg c) = literal c
DeterministicRegularExpression→Grammar ((A ⊕DetReg B) _) =
  (DeterministicRegularExpression→Grammar A) ⊕
  (DeterministicRegularExpression→Grammar B)
DeterministicRegularExpression→Grammar ((A ⊗DetReg B) _ _) =
  (DeterministicRegularExpression→Grammar A) ⊗
  (DeterministicRegularExpression→Grammar B)
DeterministicRegularExpression→Grammar (non-null A) =
  nonempty (DeterministicRegularExpression→Grammar A)
DeterministicRegularExpression→Grammar (KL*DetReg A x) =
  KL* (DeterministicRegularExpression→Grammar A)
