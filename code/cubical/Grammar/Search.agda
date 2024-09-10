{-# OPTIONS --guardedness #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum

module Grammar.Search (Alphabet : hSet ℓ-zero) where

open import Grammar Alphabet
open import Grammar.Maybe Alphabet as Maybe using (Maybe)
open import Term Alphabet
open import Monad Alphabet

private
  variable
    ℓG ℓH : Level
    g : Grammar ℓG
    h : Grammar ℓH

record Search (g : Grammar ℓG) (w : String) : Type ℓG where
  coinductive
  field
    viewSearch :
      -- done, no more results
      ( ⊤-grammar {ℓ-zero}
      -- here's one more result and there may be more
      ⊕ ((g & Search g)
      -- still searching
      ⊕ Search g)) w

open Search

view : Search g ⊢ ⊤-grammar {ℓ-zero} ⊕ ((g & Search g) ⊕ Search g)
view _ = viewSearch

unfold :
  (h ⊢ ⊤-grammar {ℓ-zero} ⊕ ((g & h) ⊕ h))
  → h ⊢ Search g
unfold f w x .viewSearch with f w x
... | inl _ = inl _
... | inr (inl (g-p , h-p)) = inr (inl (g-p , unfold f _ h-p))
... | inr (inr h-p) = inr (inr (unfold f _ h-p))

nil : ⊤-grammar {ℓ-zero} ⊢ Search g
nil = unfold ⊕-inl

cons : (g & Search g) ⊢ Search g
cons = unfold (⊕-inr ∘g ⊕-inl ∘g &-intro &-π₁ id)

wait : Search g ⊢ Search g
wait = unfold (⊕-inr ∘g ⊕-inr)

-- TODO test that these are right
-- The below seems like the only definition that could work
-- but I don't think I have good intuition on this to be sure
open Monad
SearchMonad : Monad Search
SearchMonad .return = unfold (⊕-inr ∘g ⊕-inl ∘g &-intro id id)
SearchMonad .μ =
  unfold
    (⊕-elim
      ⊕-inl
      (⊕-elim
        (⊕-elim
          (⊕-inl ∘g &-π₁)
          (⊕-elim
            (⊕-inr ∘g ⊕-inl ∘g &-par &-π₁ id)
            (⊕-inr ∘g ⊕-inr ∘g &-π₂) ∘g
          &⊕-distR) ∘g
        &⊕-distR ∘g
        &-par view id)
        (⊕-inr ∘g ⊕-inr))
    ∘g view)
SearchMonad .fmap f =
  unfold
    (⊕-elim ⊕-inl (⊕-elim (⊕-inr ∘g ⊕-inl ∘g &-par f id) (⊕-inr ∘g ⊕-inr)) ∘g
    view)

open LeftStrongMonad

SearchLeftStrongMonad : LeftStrongMonad Search
SearchLeftStrongMonad .monad = SearchMonad
SearchLeftStrongMonad .leftStrength =
  ?
  -- ⊸-intro⁻
  --   (⊕-elim
  --     (⊸-intro (nil ∘g ⊤-intro))
  --     (⊕-elim
  --       (⊸-intro {!!})
  --       (⊸-intro (⊕-inr ∘g {!!})))
  --   ∘g view)


-- -- left biased search: we exhaustively search the left before
-- -- moving to the right
-- append : Search g & Search g ⊢ Search g
-- append = {!!}

-- state := (Search g & Search h) ⊕ Search h
ext : g ⊢ Search h
  → Search g ⊢ Search h
ext {h = h} f = SearchMonad .μ ∘g SearchMonad .fmap f
