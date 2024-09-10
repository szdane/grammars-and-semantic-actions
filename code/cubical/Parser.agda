{-# OPTIONS --guardedness #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.FinSet

module Parser (Alphabet : hSet ℓ-zero)
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.List

open import Cubical.Relation.Nullary.Base

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.KleeneStar Alphabet
open import Grammar.Maybe Alphabet
open import Grammar.Exception Alphabet
open import Grammar.List Alphabet as ListG
open import Grammar.Search Alphabet as Search
open import Term Alphabet
open import Monad Alphabet

private
  variable
    ℓg ℓh : Level
    g : Grammar ℓg
    h : Grammar ℓh

open Monad
open StrongMonad
open LeftStrongMonad

Parser : Grammar ℓg → Type ℓg
Parser g = string-grammar ⊢ Search (g ⊗ string-grammar)

⊤→string : ⊤-grammar {ℓ-zero} ⊢ string-grammar
⊤→string w _ = ⌈ w ⌉

_then_ : ∀ {g : Grammar ℓg} {h : Grammar ℓh} →
  Parser g → Parser h → Parser (g ⊗ h)
_then_ {ℓg = ℓg}{ℓh = ℓh}{g = g} e e' =
  -- unfold {!⊕-!} ∘g
  {!!} ∘g
  {!!} ∘g
  SearchMonad .fmap (⊗-intro id e') ∘g
  ⊕-elim
    Search.nil
    (⊕-elim
      Search.cons
      wait) ∘g
  view ∘g
  e
  -- SearchMonad .fmap ({!!} ∘g ⊗-intro id e') ∘g
  -- SearchMonad .fmap ⊗-assoc ∘g
  -- {!!} ∘g
  -- e
  -- ListMonad .fmap ⊗-assoc ∘g
  -- ListMonad .μ ∘g
  -- ListMonad .fmap (ListLeftStrongMonad {ℓg = ℓg} .leftStrength) ∘g
  -- ListMonad .fmap (⊗-intro id e') ∘g
  -- {!!} ∘g
  -- ExceptionMonad string-grammar .fmap
  --   (ListMonad .fmap (⊗-intro id e')) ∘g
  -- e

-- -- _or_ : Parser g → Parser g → Parser g
-- -- _or_ {g = g} e e'  =
-- --   {!!}
-- --   -- caseList (g ⊗ string-grammar)
-- --   --   {!? ∘g ?!}
-- --   --   {!!} ∘g
-- --   -- e
-- -- -- ⊕-elim return (e' ∘g ⊤→string) ∘g e

-- -- -- TODO naming
-- -- -- Runs the parser, then only accepts if the parser
-- -- -- consumed all of the input string with none leftover
-- -- consumes-input : Parser g → string-grammar ⊢ ListG.List g
-- -- consumes-input {g = g} parser =
-- --   filter
-- --     (MaybeMonad .fmap ⊗-unit-r ∘g
-- --     MaybeStrongMonad .leftStrength ∘g
-- --     ⊗-intro id is-ε) ∘g
-- --   parser



-- Intuitively, we would expect a parser to return something of type
-- ListG.List (g ⊗ string-grammar)
-- However, this does not allow for alternation of parsers to be defined.
-- This is because failure to parse results in an empty list.
-- When doing case analysis to recover from a failed parse, the empty case
-- requires a term out of ⊤-grammar that we cannot define. Instead we'd wish
-- to define a term out of string-grammar (in fact, we'd like use a parser
-- as defined below)
--
-- There are a couple ways we might hope to define this sort of
-- alternation.
-- 1. Internalize the axiom ⊤-grammar ≅ string-grammar, and provide the
--    ⊤→string term (defined below). This effectively "unconsumes" the
--    string and lets us try to run the second parser
-- 2. Instead of the Result type being ListG.List (g ⊗ string-grammar), we
--    could replace it with
--      Exception string-grammar (ListG.List (g ⊗ string-grammar))
--
--    Under failure, this passes the string along instead of consuming it.
--    Although this is a little weird, because parsers that implement this
--    result type should never make use of the nil case of a
--    "successful" parse.
--
-- Although each of these hangups may be less of a real issue, and more so
-- evidence that the applicative style of combining these parsers isn't so
-- natural.
--
-- For now, we'll run with solution 2


-- TODO : To make swapping between strategies easier,
-- I want some ability to just have the result type be paramaterized
-- by some (possibly left strong) monad so that its easily configurable

-- module _
--   {ℓ-map : Level → Level}
--   {M : ∀ {ℓg} → Grammar ℓg → Grammar (ℓ-map ℓg)}
--   (the-monad : Monad M)
--   where

--   Parser : Grammar ℓg → Grammar (ℓ-map ℓg)
--   Parser g = string-grammar ⇒ M (g ⊗ string-grammar)

--   -- Potentially abstraction breaking but seemingly needed. However
--   -- this is also an axiom we've considered adding
--   ⊤→string : ⊤-grammar {ℓ-zero} ⊢ string-grammar
--   ⊤→string w _ = ⌈ w ⌉

--   open Monad

--   ParserMonad : Monad Parser
--   ParserMonad .return =
--     ⇒-intro
--       (the-monad .return ∘g
--       ⊗-intro id KL*.nil ∘g
--       ⊗-unit-r⁻ ∘g &-π₁)
--   ParserMonad .μ =
--     ⇒-intro ({!!} ∘g ⇒-app)
--   ParserMonad .fmap = {!!}

-- -- Result : (g : Grammar ℓg) → Grammar ℓg
-- -- Result g =
-- --   Exception string-grammar (ListG.List (g ⊗ string-grammar))

-- -- Parser' : Grammar ℓg → Grammar ℓg
-- -- Parser' g = string-grammar ⇒ Result g

-- -- Parser'Monad : Monad Parser'
-- -- Parser'Monad .return = ⇒-intro ({!!} ∘g &-π₁)
-- -- Parser'Monad .μ = {!!}
-- -- Parser'Monad .fmap = {!!}

-- -- Parser : (g : Grammar ℓg) → Type ℓg
-- -- Parser g = string-grammar ⊢ Result g

-- -- is-ε : string-grammar ⊢ Maybe ε-grammar
-- -- is-ε = caseKL* char just nothing

-- -- _then_ : ∀ {g : Grammar ℓg} {h : Grammar ℓh} →
-- --   Parser g → Parser h → Parser (g ⊗ h)
-- -- _then_ {ℓg = ℓg}{ℓh = ℓh}{g = g} e e' =
--   -- ListMonad .fmap ⊗-assoc ∘g
--   -- ListMonad .μ ∘g
--   -- ListMonad .fmap (ListLeftStrongMonad {ℓg = ℓg} .leftStrength) ∘g
--   -- ListMonad .fmap (⊗-intro id e') ∘g
--   -- {!!} ∘g
--   -- ExceptionMonad string-grammar .fmap
--   --   (ListMonad .fmap (⊗-intro id e')) ∘g
--   -- e

-- -- _or_ : Parser g → Parser g → Parser g
-- -- _or_ {g = g} e e'  =
-- --   {!!}
-- --   -- caseList (g ⊗ string-grammar)
-- --   --   {!? ∘g ?!}
-- --   --   {!!} ∘g
-- --   -- e
-- -- -- ⊕-elim return (e' ∘g ⊤→string) ∘g e

-- -- -- TODO naming
-- -- -- Runs the parser, then only accepts if the parser
-- -- -- consumed all of the input string with none leftover
-- -- consumes-input : Parser g → string-grammar ⊢ ListG.List g
-- -- consumes-input {g = g} parser =
-- --   filter
-- --     (MaybeMonad .fmap ⊗-unit-r ∘g
-- --     MaybeStrongMonad .leftStrength ∘g
-- --     ⊗-intro id is-ε) ∘g
-- --   parser


-- -- -- -- Potentially abstraction breaking but seemingly needed. However
-- -- -- -- this is also an axiom we've considered adding
-- -- -- ⊤→string : ∀ {ℓg} → Term {ℓg} ⊤-grammar string-grammar
-- -- -- ⊤→string w _ = ⌈ w ⌉

-- -- -- Parser : (g : Grammar ℓg) → Type ℓg
-- -- -- Parser g = string-grammar ⊢ Maybe (g ⊗ string-grammar)


-- -- -- TODO this is hella unsafe. Change to not return ⊤, but string-grammar
-- -- -- Moreover, change Parser to be configurable w different monad choices
-- -- -- Try the first parser. If it fails try the second

-- -- -- infixr 8 _then_

-- -- -- parseε : Parser ε-grammar
-- -- -- parseε =
-- -- --   just ∘g
-- -- --   ⊗-unit-l⁻

-- -- -- parseChar : (c : ⟨ Alphabet ⟩) → Parser (literal c)
-- -- -- parseChar c =
-- -- --   caseKL* char
-- -- --     nothing
-- -- --     (λ _ (split , (c' , lit) , ⌈w⌉) →
-- -- --       decRec
-- -- --         (λ c≡c' → just {g = literal c ⊗ string-grammar}
-- -- --           _ (split ,
-- -- --              subst (λ a → split .fst .fst ≡ [ a ]) (sym c≡c') lit ,
-- -- --              ⌈w⌉))
-- -- --         (λ _ →
-- -- --           nothing
-- -- --             {g = char ⊗ string-grammar}
-- -- --             {h = literal c ⊗ string-grammar}
-- -- --               _ (split , (c' , lit) , ⌈w⌉))
-- -- --         (isFinSet→Discrete isFinSetAlphabet c c')
-- -- --     )
