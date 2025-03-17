{-# OPTIONS --erased-cubical --erasure #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Epsilon.Base
  (Alphabet : Type ℓ-zero)
  (isSetAlphabet : isSet Alphabet)
  where

open import Agda.Builtin.Unit as Unit
open import Cubical.Data.List
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet isSetAlphabet
-- open import Grammar.HLevels.Base Alphabet
-- open import Grammar.Lift.Base Alphabet
open import Term.Base Alphabet isSetAlphabet
open import Term.Nullary Alphabet isSetAlphabet

private
  variable
    ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

data my⊥ : Type where

opaque
  ε : Grammar ℓ-zero
  ε w = w ≡ []
  -- ε [] = Unit.⊤
  -- ε (x ∷ w) = my⊥

  -- ε-intro : ε⊢ ε
  -- ε-intro = refl

--   ε-elim : ∀ {A : Grammar ℓA} → ε⊢ A → ε ⊢ A
--   ε-elim {A = A} A[] w w≡[] = subst A (sym w≡[]) A[]

--   ε-elim-natural : ∀ {A : Grammar ℓA} → (x : ε⊢ A) →
--     (f : A ⊢ B) →
--     f ∘g ε-elim {A = A} x ≡ ε-elim (f ∘ε x)
--   ε-elim-natural {B = B} {A = A} x f = funExt λ w → funExt λ p →
--     J (λ w' w'≡ → (f ∘g ε-elim x) w' (sym w'≡) ≡ ε-elim {A = B}(f ∘ε x) w' (sym w'≡))
--       (cong (f []) (transportRefl x) ∙ sym (substRefl {A = A []} {B = λ _ → B []} {x = x} (f [] x)))
--       (sym p)

--   ε-β : ∀ (Ap : ε⊢ A) → ε-elim {A = A} Ap ∘ε ε-intro ≡ Ap
--   ε-β {A = A} Ap = transportRefl Ap

--   isLangε : isLang ε
--   isLangε _ _ _ = isSetString _ _ _ _

--   isSetGrammarε : isSetGrammar ε
--   isSetGrammarε = isLang→isSetGrammar isLangε

--   ε-length0 : ∀ w → ε w → length w ≡ 0
--   ε-length0 [] p = refl
--   ε-length0 (x ∷ w) p = Empty.rec (¬cons≡nil p)

-- ε* : ∀ {ℓ : Level} → Grammar ℓ
-- ε* {ℓ = ℓ} = LiftG ℓ ε

-- isLangε* : ∀ {ℓ} → isLang (ε* {ℓ})
-- isLangε* = isLangLift isLangε

-- isSetGrammarε* : ∀ {ℓ} → isSetGrammar (ε* {ℓ})
-- isSetGrammarε* = isLang→isSetGrammar isLangε*
