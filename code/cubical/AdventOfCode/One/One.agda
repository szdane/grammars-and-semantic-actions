open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module AdventOfCode.One.One where

-- import Agda.Builtin.String as BuiltinStr
-- import IO.Primitive.Core as Prim
-- import Data.Unit.Base as Unit'
-- open import IO
-- open import IO.Finite

open import Cubical.Data.List

open import String.ASCII
open import String.ASCII.NoWhitespace
open import String.Unicode
open import String.SubAlphabet
open import AdventOfCode.One.Input

open DecodeUnicode ASCII Unicode→ASCII

open import Grammar

s : String ASCII
s = mkString input

_ : s ≡ a^ ∷ SPACE ∷ SPACE ∷ b^ ∷ NEWLINE ∷ c^ ∷ SPACE ∷ SPACE ∷ d^ ∷ []
_ = refl

s' : String ASCIINW
s' = Alphabet→SubAlphabet' ASCII NWCharFun s

_ : s' ≡ (a^ , _) ∷ (b^ , _) ∷ (c^ , _) ∷ (d^ , _) ∷ []
_ = refl

open import Term ASCII
