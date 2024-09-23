{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Cubes.Base

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.List
open import Cubical.Data.Empty as Empty hiding (⊥;⊥*)
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.Negation Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.String Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓS : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl


open isStrongEquivalence

-- A grammar is unambiguous if it is subterminal --- i.e.
-- if the unique map to the terminal object (⊤) is a
-- monomorphism
unambiguous : Grammar ℓg → Typeω
unambiguous {ℓg = ℓg} g = isMono {g = g}{h = ⊤} (⊤-intro {g = g})

-- Follows from being subterminal: a grammar is unambiguous
-- if there is at most one morhpism from any
-- other fixed object into it
-- This definition is likely easier to invoke in proofs
unambiguous' : Grammar ℓg → Typeω
unambiguous' g = ∀ {ℓh} {h : Grammar ℓh} → (e e' : h ⊢ g) → e ≡ e'

unambiguous→unambiguous' : unambiguous g → unambiguous' g
unambiguous→unambiguous' unambig e e' =
  unambig e e'
    (sym (is-terminal-⊤ .snd (⊤-intro ∘g e)) ∙
         is-terminal-⊤ .snd (⊤-intro ∘g e') )

unambiguous'→unambiguous : unambiguous' g → unambiguous g
unambiguous'→unambiguous unambig' e e' ≡! = unambig' e e'

module EXTERNAL where
  -- This is not intended to be used in the library
  -- This is the external notion of what we'd expected an unambiguous
  -- grammar to be, that each input string is parsed uniquely

  unambiguous-ext : Grammar ℓg → Type ℓg
  unambiguous-ext g = ∀ w → isProp (g w)

  unambiguous-ext→unambiguous : unambiguous-ext g → unambiguous g
  unambiguous-ext→unambiguous {g = g} unambig' e e' _ =
    funExt (λ w → funExt (λ x → unambig' w (e w x) (e' w x)))

  module _ (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where
    opaque
      unfolding uniquely-supported-⌈w⌉ internalize ⊤
      unambiguous→unambiguous-ext : unambiguous g → unambiguous-ext g
      unambiguous→unambiguous-ext {g = g} unambig w pg pg' =
        isMono→injective unambig w pg pg' refl
        where
        pick-parse : ∀ w' (h : Grammar ℓh) → h w' → ⌈ w' ⌉ ⊢ h
        pick-parse w' h p w'' x =
          subst h (uniquely-supported-⌈w⌉ isFinSetAlphabet w' w'' x) p

        isMono→injective : {e : h ⊢ ⊤} →
          isMono e → ∀ w p p' → e w p ≡ e w p' → p ≡ p'
        isMono→injective {h = h}{e = e} mono-e w p p' ewp≡ewp' =
          sym (transportRefl p) ∙
          cong (λ a → transp (λ i → h (a i)) i0 p) (isSetString _ w refl _) ∙
          funExt⁻
            (funExt⁻ (mono-e (pick-parse w h p) (pick-parse w h p') refl) w)
              (internalize w) ∙
          cong (λ a → transp (λ i → h (a i)) i0 p') (isSetString _ w _ refl) ∙
          transportRefl p'

  -- Thus the internal and external notions of unambiguity are logically
  -- equivalent. Moreover, each of these can be show to be prop-valued
  -- (up to rewriting the definition of mono to not be a Typeω), so the
  -- logical equivalence can be lifted to an iso

totallyParseable : Grammar ℓg → Type (ℓ-suc ℓg)
totallyParseable {ℓg = ℓg} g =
  Σ[ g' ∈ Grammar ℓg ] StrongEquivalence (g ⊕ g') ⊤

open StrongEquivalence

opaque
  unfolding ⊤-intro
  totallyParseable→unambiguous :
    totallyParseable g → unambiguous g
  totallyParseable→unambiguous parseable =
    Mono∘g ⊕-inl _
      (isStrongEquivalence→isMono
        (parseable .snd .fun)
        (StrongEquivalence→isStrongEquivalence _ _ (parseable .snd)))
      isMono-⊕-inl

decidable : Grammar ℓg → Type ℓg
decidable g = StrongEquivalence (g ⊕ (¬ g)) ⊤

decidable→totallyParseable :
  decidable g → totallyParseable g
decidable→totallyParseable dec-g = _ , dec-g

opaque
  unfolding ⊤
  unambiguous⊤ : unambiguous ⊤
  unambiguous⊤ e e' _ = refl

opaque
  unfolding ⊤*
  unambiguous⊤* : ∀ {ℓg} → unambiguous (⊤* {ℓg})
  unambiguous⊤* e e' _ = refl

unambiguous⊥ : unambiguous ⊥
unambiguous⊥ {k = k} e e' !∘e≡!∘e' =
  is-initial→propHoms (g⊢⊥→is-initial e) _ _

opaque
  unfolding ε literal
  unambiguous-ext-string : EXTERNAL.unambiguous-ext string
  unambiguous-ext-string [] (nil .[] x) (nil .[] y) =
    cong (nil []) (isSetString _ _ _ _)
  unambiguous-ext-string [] (nil .[] _) (cons .[] x) =
    Empty.rec
      (¬nil≡cons
        (x .fst .snd ∙
          cong (_++ x .fst .fst .snd)
            (x .snd .fst .snd)))
  unambiguous-ext-string [] (cons .[] x) _ =
    Empty.rec
      (¬nil≡cons
        (x .fst .snd ∙
          cong (_++ x .fst .fst .snd)
            (x .snd .fst .snd)))
  unambiguous-ext-string (c ∷ w) (nil .(c ∷ w) x) (nil .(c ∷ w) y) =
    Empty.rec (¬nil≡cons (sym x))
  unambiguous-ext-string (c ∷ w) (nil .(c ∷ w) x) (cons .(c ∷ w) y) =
    Empty.rec (¬nil≡cons (sym x))
  unambiguous-ext-string (c ∷ w) (cons .(c ∷ w) x) (nil .(c ∷ w) y) =
    Empty.rec (¬nil≡cons (sym y))
  unambiguous-ext-string (c ∷ w) (cons .(c ∷ w) x) (cons .(c ∷ w) y) =
    cong (cons (c ∷ w))
      (⊗≡ x y
        (≡-× (x .snd .fst .snd ∙
             cong ([_]) (sym c≡x₂₁₁ ∙ c≡y₂₁₁) ∙
             sym (y .snd .fst .snd))
             (sym w≡x₁₁₂ ∙ w≡y₁₁₂))
        (ΣPathP ((ΣPathP
          ((sym c≡x₂₁₁ ∙ c≡y₂₁₁) ,
          isProp→PathP (λ i → isSetString _ _) _ _)) ,
          isProp→PathP
            (λ i → isProp-at-w'i i)
            (x .snd .snd) (y .snd .snd))))
    where
      c≡x₂₁₁ : c ≡ x .snd .fst .fst
      c≡x₂₁₁ =
        cons-inj₁
            (x .fst .snd ∙ cong (_++ x .fst .fst .snd) (x .snd .fst .snd))

      c≡y₂₁₁ : c ≡ y .snd .fst .fst
      c≡y₂₁₁ =
        cons-inj₁
            (y .fst .snd ∙ cong (_++ y .fst .fst .snd) (y .snd .fst .snd))

      w≡x₁₁₂ : w ≡ x .fst .fst .snd
      w≡x₁₁₂ =
        cons-inj₂ (x .fst .snd ∙ (cong (_++ x .fst .fst .snd) (x .snd .fst .snd)) )

      w≡y₁₁₂ : w ≡ y .fst .fst .snd
      w≡y₁₁₂ =
        cons-inj₂ (y .fst .snd ∙ (cong (_++ y .fst .fst .snd) (y .snd .fst .snd)) )

      w' : x .fst .fst .snd ≡ y .fst .fst .snd
      w' =
        (λ i →
        (≡-×
        (x .snd .fst .snd ∙
         (λ i₁ → [ ((λ i₂ → c≡x₂₁₁ (~ i₂)) ∙ c≡y₂₁₁) i₁ ]) ∙
         (λ i₁ → y .snd .fst .snd (~ i₁)))
        ((λ i₁ → w≡x₁₁₂ (~ i₁)) ∙ w≡y₁₁₂) i .snd))

      isProp-at-w : isProp (KL* char w)
      isProp-at-w = unambiguous-ext-string w

      -- There has to be a nicer way to extract this goal out
      -- from isProp (KL* char w) because w is equal to each of
      -- the endpoints of w'
      -- I guessed at what the path variables need to be below
      -- and somehow it worked
      isProp-at-w'i : (i : I) → isProp (KL* char (w' i))
      isProp-at-w'i i =
        transport
        (cong (λ z → isProp (KL* char z))
          (w≡x₁₁₂ ∙ (λ j → (w') (i ∧ j))))
        isProp-at-w

unambiguous-string : unambiguous string
unambiguous-string =
  EXTERNAL.unambiguous-ext→unambiguous unambiguous-ext-string

string≅⊤ : StrongEquivalence string ⊤
string≅⊤ .fun = ⊤-intro
string≅⊤ .inv = ⊤→string
string≅⊤ .sec =
  unambiguous→unambiguous' unambiguous⊤ _ _
string≅⊤ .ret = unambiguous→unambiguous' unambiguous-string _ _

open isStrongEquivalence
opaque
  unfolding ⊤-intro
  unambiguous≅ : StrongEquivalence g h → unambiguous g → unambiguous h
  unambiguous≅ {g = g}{h = h} eq unambig-g e e' !≡ =
    Mono∘g {h = g} (eq .inv) (⊤-intro {g = g})
      unambig-g
      (isStrongEquivalence→isMono
        (eq .inv) (isStrEq (eq .fun) (eq .ret) (eq .sec)))
      e e' refl

module _
  {A : Type ℓS} {h : A → Grammar ℓh}
  {isSetA : isSet A}
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where
  unambiguousΣ :
    unambiguous (LinΣ[ a ∈ A ] h a) →
      (a : A)  → unambiguous (h a)
  unambiguousΣ unambigΣ a f f' !≡ =
    isMono-LinΣ-intro {A = A}{h = h}{isSetA = isSetA}
      isFinSetAlphabet a
      f f'
      (unambigΣ (LinΣ-intro a ∘g f) (LinΣ-intro a ∘g f')
        -- Need to change the endpoints of !≡ to line up with the
        -- ⊤-intro at the proper domain
        (unambiguous→unambiguous' unambiguous⊤ _ _ ∙
        !≡ ∙
        sym (unambiguous→unambiguous' unambiguous⊤ _ _)))
