open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Grammar.Literal.Parseable (Alphabet : hSet ℓ-zero) where

open import Cubical.Relation.Nullary.Base hiding (¬_)
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Relation.Nullary.DecidablePropositions.More

open import Cubical.Data.List hiding (rec)
open import Cubical.Data.FinSet
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Empty as Empty

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Distributivity Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Sum.Binary.Cartesian Alphabet
open import Grammar.String Alphabet
open import Grammar.Literal.Base Alphabet
open import Grammar.Literal.Properties Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.HLevels Alphabet hiding (⟨_⟩)
open import Term.Base Alphabet

open StrongEquivalence
module _ (c : ⟨ Alphabet ⟩) where
  different-char : Grammar ℓ-zero
  different-char =
    ⊕[ c' ∈ ⟨ Alphabet ⟩ ] ⊕[ x ∈ (c ≡ c' → Empty.⊥ ) ] ＂ c' ＂

  different-char→char : different-char ⊢ char
  different-char→char = ⊕ᴰ-elim (λ c' → ⊕ᴰ-elim λ _ → σ c')

  disjoint-different-char : disjoint ＂ c ＂ different-char
  disjoint-different-char =
    ⊕ᴰ-elim (λ c' →
      ⊕ᴰ-elim (λ c≢c' → ⊕ᴰ-elim (λ c≡c' → Empty.rec (c≢c' c≡c')) ∘g same-literal c c')
      ∘g &⊕ᴰ-distR≅ .fun
    )
    ∘g &⊕ᴰ-distR≅ .fun

  opaque
    unfolding literal
    isLang-different-char : isLang different-char
    isLang-different-char w (c , _ , p) (c' , _ , p') =
      ΣPathP ((cons-inj₁ ((sym p) ∙ p')) ,
      (ΣPathP ((isProp→PathP (λ i → isProp→ Empty.isProp⊥) _ _) ,
      isProp→PathP (λ i → isLangLiteral _ _) p p')))

  unambiguous-different-char : unambiguous different-char
  unambiguous-different-char = EXTERNAL.isLang→unambiguous isLang-different-char

  literal-complement : Grammar ℓ-zero
  literal-complement =
    ε ⊕
    different-char ⊕
    (char ⊗ (char +))

  module _ (disc : Discrete ⟨ Alphabet ⟩) where
    lit≅ : ＂ c ＂ ⊕ different-char ≅ char
    lit≅ .fun = ⊕-elim (literal→char c) different-char→char
    lit≅ .inv =
      ⊕ᴰ-elim (λ c' →
        decRec
          (J (λ c' c≡c' → ＂ c' ＂ ⊢ ＂ c ＂ ⊕ _) inl)
          (λ c≢c' → inr ∘g σ c' ∘g σ c≢c')
          (disc c c')
      )
    lit≅ .sec = unambiguous-char _ _
    lit≅ .ret =
      unambiguous⊕
        disjoint-different-char
        (unambiguous-literal c)
        unambiguous-different-char
        _
        _

    string≅lit⊕complement : string ≅ ＂ c ＂ ⊕ literal-complement
    string≅lit⊕complement =
      unroll-string≅
      ≅∙ ⊕≅ id≅ unroll-char+≅
      ≅∙ ⊕≅ id≅ (⊕≅ (sym≅ lit≅) id≅)
      ≅∙ sym≅ ⊕-assoc≅
      ≅∙ ⊕≅ ⊕-swap≅ id≅
      ≅∙ ⊕≅ ⊕-assoc≅ id≅
      ≅∙ ⊕-assoc≅
      ≅∙ ⊕≅ id≅ (
        ⊕≅ ⊕-swap≅ id≅
        ≅∙ ⊕-assoc≅
        )

    totallyParseable'Literal : totallyParseable' ＂ c ＂
    totallyParseable'Literal .fst = literal-complement
    totallyParseable'Literal .snd = sym≅ string≅lit⊕complement
