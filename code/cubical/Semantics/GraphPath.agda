{-# OPTIONS -WnoUnsupportedIndexedMatch --no-require-unique-meta-solutions #-}
module Semantics.GraphPath where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

open import Cubical.Data.Sum as Sum hiding (elim ; rec ; map)
open import Cubical.Data.Empty as ⊥ hiding (elim ; rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat as Nat hiding (elim)
import      Cubical.Data.Nat.Order.Recursive as NatOrd
open import Cubical.Data.Sigma

open import Cubical.Data.FinData
open import Cubical.Data.DecFin

open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Semantics.Helper
private
  variable
    ℓ ℓ' : Level

record directedGraph : Type (ℓ-suc ℓ) where
  field
    states : FinSet ℓ
    directed-edges : FinSet ℓ
    src : ⟨ directed-edges ⟩ → ⟨ states ⟩
    dst : ⟨ directed-edges ⟩ → ⟨ states ⟩

  record GraphWalk : Type ℓ where
    field
      length : ℕ
      vertices : Fin (suc length) → ⟨ states ⟩
      edges : Fin length → ⟨ directed-edges ⟩
      compat-src : (i : Fin length) → src (edges i) ≡ vertices (weakenFin i)
      compat-dst : (i : Fin length) → dst (edges i) ≡ vertices (suc i)

  record GraphPath (ℓ' : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
    field
      length : ℕ
      isVisited : ⟨ states ⟩ → DecProp ℓ'

    visited : FinSet (ℓ-max ℓ ℓ')
    visited = (Σ[ state ∈ ⟨ states ⟩ ] ⟨ isVisited state ⟩) , isFinSetΣ {!str states!} {!!} --Σ[ state ∈ ⟨ states ⟩ ] ⟨ isVisited state ⟩ , ?

    field
      vertices : Fin (suc length) ≃ ⟨ visited ⟩
      edges : Fin length → ⟨ directed-edges ⟩
      compat-src : (i : Fin length) → src (edges i) ≡ (equivFun vertices) (weakenFin i) .fst
      compat-dst : (i : Fin length) → dst (edges i) ≡ (equivFun vertices) (suc i) .fst

    verticesOrd : FinOrd (ℓ-max ℓ ℓ')
    verticesOrd = ⟨ visited ⟩ , (suc length) , (invEquiv vertices)

  module _ where
    open GraphWalk
    open GraphPath

    Path→Walk : GraphPath ℓ' → GraphWalk
    Path→Walk path .length = path .length
    Path→Walk path .vertices = fst ∘ equivFun (path .vertices)
    Path→Walk path .edges = path .edges
    Path→Walk path .compat-src = path .compat-src
    Path→Walk path .compat-dst = path .compat-dst

    Walk→Path : GraphWalk → GraphPath {!!}
    Walk→Path walk .length = walk .length
    Walk→Path walk .isVisited state = {!!}
    Walk→Path walk .vertices = {!!}
    Walk→Path walk .edges = {!!}
    Walk→Path walk .compat-src = {!!}
    Walk→Path walk .compat-dst = {!!}

    --   -- "Efficient" graph walks, with length no more than the number of vertices
    --   -- The idea is that there are finitely many fast walks, and any walk is equivalent to one of them
    --   FastWalk : states .fst → states .fst → Type ℓ
    --   FastWalk start end = Σ[ n ∈ Fin bound ] Walk[ toℕ n ] start end

    --   FastWalkIsFinSet : ∀ {start end} → isFinSet (FastWalk start end)
    --   FastWalkIsFinSet = isFinSetΣ (_ , isFinSetFin) λ _ → _ , Walk[]IsFinSet

    --   FastWalk→Walk : ∀ {start end} → FastWalk start end → Walk start end
    --   FastWalk→Walk (_ , walk[]) = Walk[]→Walk walk[]

    --   -- The core of the proof, that any walk is equivalent to a fast walk
    --   Walk→FastWalk : ∀ {start end} → Walk start end → FastWalk start end
    --   Walk→FastWalk = Walk.rec {!!}
    -- open DecReachability public hiding (bound)

    -- -- Walk[_]Dec : ∀ n {start end} → Dec ∥ Walk[ n ] start end ∥₁
    -- -- Walk[ n ]Dec = isFinSet→Dec∥∥ $ Walk[ n ]IsFinSet

    -- -- FastWalk→reachable : ∀ start end → FastWalk start end → reachable start end
    -- -- FastWalk→reachable start end (_ , walk) = Conv.Walk[ _ ]→reachable walk

    -- -- reachable→Walk[] : ∀ start end → reachable start end → Σ[ n ∈ ℕ ] Walk[ n ] start end
    -- -- reachable→Walk[] = {!!}

    -- -- reachable→FastWalk : ∀ start end → reachable start end → FastWalk start end
    -- -- reachable→FastWalk = {!!}

    -- -- ∥reachable∥≃∥FastWalk∥ : ∀ start end → ∥ reachable start end ∥₁ ≃ ∥ FastWalk start end ∥₁
    -- -- ∥reachable∥≃∥FastWalk∥ start end = propBiimpl→Equiv isPropPropTrunc isPropPropTrunc
    -- --                                       (PT.map $ reachable→FastWalk start end)
    -- --                                       (PT.map $ FastWalk→reachable start end)

    -- -- isSetStates : isSet (states .fst)
    -- -- isSetStates = isFinSet→isSet (states .snd)

    -- -- isPropStates≡ : {v : states .fst} → isProp (v ≡ v)
    -- -- isPropStates≡ = isSetStates _ _

    -- reachDecProp :
    --   ∀ start end → DecProp ℓ
    -- fst (fst (reachDecProp start end)) = {!!} -- ∥ reachable start end ∥₁
    -- snd (fst (reachDecProp start end)) = {!!} -- isPropPropTrunc
    -- snd (reachDecProp start end) = {!!}
    --   -- -- Branch on if the start state is equal to the end state
    --   -- decRec
    --   --   -- if yes then we have a path
    --   --   (λ start=end → yes ∣ transport (cong (λ a → reachable start a) start=end) nil ∣₁)
    --   --   -- if no then we have to search
    --   --   (λ start≠end → {!!})
    --   --   (isFinSet→Discrete (states .snd) start end)

    -- -- Set of reachable states from a start states
    -- -- are the ones for which there exists a path
    -- reachableFrom : states .fst → FinSetDecℙ states .fst
    -- reachableFrom start end = DecProp∃ states (reachDecProp start)
