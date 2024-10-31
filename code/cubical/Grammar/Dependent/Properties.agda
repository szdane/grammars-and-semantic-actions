open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Top Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet

private
  variable
    ℓg ℓh ℓS : Level

open StrongEquivalence
module _ {A : Type ℓS} {g : Grammar ℓg}{h : A → Grammar ℓh} where
  ⊕ᴰ-distL-inv : (⊕[ a ∈ A ] (h a ⊗ g)) ⊢ ((⊕[ a ∈ A ] h a) ⊗ g)
  ⊕ᴰ-distL-inv = ⊕ᴰ-elim λ a → ⊕ᴰ-in a ,⊗ id

  -- This is nice because it's derivable but it has annoying
  -- definitional behavior because of the ⟜
  ⊕ᴰ-distL-fun' : ((⊕[ a ∈ A ] h a) ⊗ g) ⊢ (⊕[ a ∈ A ] (h a ⊗ g))
  ⊕ᴰ-distL-fun' = ⟜-intro⁻ (⊕ᴰ-elim λ a → ⟜-intro (⊕ᴰ-in a))
  opaque
    unfolding _⊗_ ⊗-intro
    -- these definitions have better definitional behavior.
    ⊕ᴰ-distL-fun : ((⊕[ a ∈ A ] h a) ⊗ g) ⊢ (⊕[ a ∈ A ] (h a ⊗ g))
    ⊕ᴰ-distL-fun w (s , (a , x) , y) = a , ((s , (x , y)))

    ⊕ᴰ-distL :
      StrongEquivalence
        ((⊕[ a ∈ A ] h a) ⊗ g)
        (⊕[ a ∈ A ] (h a ⊗ g))
    ⊕ᴰ-distL .fun = ⊕ᴰ-distL-fun
    ⊕ᴰ-distL .inv = ⊕ᴰ-distL-inv
    ⊕ᴰ-distL .sec = refl
    ⊕ᴰ-distL .ret = refl

    ⊕ᴰ-distR :
      StrongEquivalence
        (g ⊗ (⊕[ a ∈ A ] h a))
        (⊕[ a ∈ A ] (g ⊗ h a))
    ⊕ᴰ-distR .fun w (s , x , (a , y)) = a , ((s , (x , y)))
    ⊕ᴰ-distR .inv w (a , (s , (x , y))) = s , (x , (a , y))
    ⊕ᴰ-distR .sec = refl
    ⊕ᴰ-distR .ret = refl

  &ᴰ-strengthL : (&[ a ∈ A ] h a) ⊗ g ⊢ &[ a ∈ A ] (h a ⊗ g)
  &ᴰ-strengthL = &ᴰ-intro λ a → &ᴰ-π a ,⊗ id

  &ᴰ-strengthR : g ⊗ (&[ a ∈ A ] h a) ⊢ &[ a ∈ A ] (g ⊗ h a)
  &ᴰ-strengthR = &ᴰ-intro (λ a → id ,⊗ &ᴰ-π a)

module _ {ℓ ℓ' ℓ''}{X : Type ℓ} {Y : X → Type ℓ'}{A : ∀ x → Y x → Grammar ℓ''}
  where
  ⊕ᴰ&ᴰ-dist-inv :
    ⊕[ f ∈ (∀ x → Y x) ] &[ x ∈ X ] A x (f x) ⊢ &[ x ∈ X ] ⊕[ y ∈ Y x ] A x y
  ⊕ᴰ&ᴰ-dist-inv = ⊕ᴰ-elim λ f → &ᴰ-intro λ x → ⊕ᴰ-in (f x) ∘g &ᴰ-π x
  opaque
    ⊕ᴰ&ᴰ-dist-fun :
      &[ x ∈ X ] ⊕[ y ∈ Y x ] A x y ⊢ ⊕[ f ∈ (∀ x → Y x) ] &[ x ∈ X ] A x (f x)
    ⊕ᴰ&ᴰ-dist-fun w f = (λ x → f x .fst) , λ x → f x .snd
    
    ⊕ᴰ&ᴰ-dist : StrongEquivalence
      (&[ x ∈ X ] ⊕[ y ∈ Y x ] A x y)
      (⊕[ f ∈ (∀ x → Y x) ] &[ x ∈ X ] A x (f x))
    ⊕ᴰ&ᴰ-dist .fun = ⊕ᴰ&ᴰ-dist-fun
    ⊕ᴰ&ᴰ-dist .inv = ⊕ᴰ&ᴰ-dist-inv
    ⊕ᴰ&ᴰ-dist .sec = refl
    ⊕ᴰ&ᴰ-dist .ret = refl
module _
  {A : Type ℓS} {h : A → Grammar ℓh}
  (isSetA : isSet A)
  where

  isMono-⊕ᴰ-in : (a : A) → isMono (⊕ᴰ-in {h = h} a)
  isMono-⊕ᴰ-in a e e' !∘e=!∘e' =
    funExt λ w → funExt λ p →
      sym (transportRefl (e w p)) ∙
      Σ-contractFst (refl , (isSetA _ _ _)) .fst
        (PathΣ→ΣPathTransport _ _ (funExt⁻ (funExt⁻ !∘e=!∘e' w) p))

  unambiguous'⊕ᴰ :
    unambiguous' (⊕[ a ∈ A ] h a) →
      (a : A)  → unambiguous' (h a)
  unambiguous'⊕ᴰ unambig⊕ a f f' !≡ =
    isMono-⊕ᴰ-in a f f'
      (unambig⊕ (LinΣ-intro a ∘g f) (LinΣ-intro a ∘g f')
        -- Need to change the endpoints of !≡ to line up with the
        -- ⊤-intro at the proper domain
        (unambiguous⊤ _ _ ∙ !≡ ∙ sym (unambiguous⊤ _ _)))

  unambiguous⊕ᴰ : unambiguous (⊕[ a ∈ A ] h a) → (a : A) →
    unambiguous (h a)
  unambiguous⊕ᴰ unambig⊕ a =
    unambiguous'→unambiguous
      (unambiguous'⊕ᴰ (unambiguous→unambiguous' unambig⊕) a)

module _
  {X : Type ℓS} {A : X → Grammar ℓh}
  where
  isSetGrammar&ᴰ : (∀ x → isSetGrammar (A x)) → isSetGrammar (&ᴰ A)
  isSetGrammar&ᴰ isSetGrammarA w = isSetΠ λ x → isSetGrammarA x w

  isSetGrammar⊕ᴰ : isSet X → (∀ x → isSetGrammar (A x)) → isSetGrammar (⊕ᴰ A)
  isSetGrammar⊕ᴰ isSetX isSetGrammarA w = isSetΣ isSetX (λ x → isSetGrammarA x w)
