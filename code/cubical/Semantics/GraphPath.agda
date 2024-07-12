module Semantics.GraphPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.SumFin hiding (fsuc)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Helper
private
  variable
    ℓ ℓ' : Level

record directedGraph : Type (ℓ-suc ℓ) where
  field
    states : FinSet ℓ
    directed-edges : FinSet ℓ
    src : directed-edges .fst → states .fst
    dst : directed-edges .fst → states .fst

  data reachable (start : states .fst) :
    (end : states .fst) → Type ℓ where
    nil : reachable start start
    cons : ∀ (e : directed-edges .fst) →
      reachable start (src e) →
      reachable start (dst e)

  reachDecProp :
    ∀ start end → DecProp ℓ
  fst (fst (reachDecProp start end)) = ∥ reachable start end ∥₁
  snd (fst (reachDecProp start end)) = isPropPropTrunc
  snd (reachDecProp start end) =
    -- Branch on if the start state is equal to the end state
    decRec
      -- if yes then we have a path
      (λ start=end → yes ∣ transport (cong (λ a → reachable start a) start=end) nil ∣₁)
      -- if no then we have to search
      (λ start≠end → {!!})
      (isFinSet→Discrete (states .snd) start end)

  -- Set of reachable states from a start states
  -- are the ones for which there exists a path
  reachableFrom : states .fst → FinSetDecℙ states .fst
  reachableFrom start end = DecProp∃ states (reachDecProp start)
