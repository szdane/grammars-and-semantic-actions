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

  adjacent : states .fst → states .fst → Type ℓ
  adjacent u v = Σ[ e ∈ directed-edges .fst ] (src e ≡ u) × (dst e ≡ v)

  adjacentIsFinSet : ∀ u v → isFinSet (adjacent u v)
  adjacentIsFinSet u v = isFinSetΣ directed-edges λ e → _ ,
                         isFinSet× (_ , isFinSet≡ states _ _) (_ , isFinSet≡ states _ _)

  data reachable (start : states .fst) :
    (end : states .fst) → Type ℓ where
    nil : reachable start start
    cons : ∀ (e : directed-edges .fst) →
      reachable start (src e) →
      reachable start (dst e)

  WalkOfLen : ℕ → states .fst → states .fst → Type ℓ
  WalkOfLen 0 start end = start ≡ end
  WalkOfLen (suc n) start end = Σ[ v ∈ states .fst ] Σ[ start⟶v ∈ WalkOfLen n start v ] adjacent v end

  WalkOfLenIsFinSet : ∀ n start end → isFinSet (WalkOfLen n start end)
  WalkOfLenIsFinSet 0 start end = isFinSet≡ states _ _
  WalkOfLenIsFinSet (suc n) start end = isFinSetΣ states λ v → _ ,
                                      isFinSetΣ (_ , WalkOfLenIsFinSet n start v) λ start⟶v → _ ,
                                      adjacentIsFinSet _ _

  WalkOfLenDec : ∀ n start end → Dec ∥ WalkOfLen n start end ∥₁
  WalkOfLenDec n start end = isFinSet→Dec∥∥ $ WalkOfLenIsFinSet n start end

  BoundedWalk : states .fst → states .fst → Type ℓ
  BoundedWalk start end = Σ[ n ∈ Fin (card states) ] WalkOfLen (toℕ n) start end

  BoundedWalkIsFinSet : ∀ start end → isFinSet (BoundedWalk start end)
  BoundedWalkIsFinSet start end = isFinSetΣ (_ , isFinSetFin) λ _ → _ , WalkOfLenIsFinSet _ _ _

  WalkOfLen→reachable : ∀ {n} start end → WalkOfLen n start end → reachable start end
  WalkOfLen→reachable {n = 0} start end start≡end = subst (reachable start) start≡end nil
  WalkOfLen→reachable {n = suc n} start end (v , start⟶v , e , srce≡v , deste≡end) =
    let path = WalkOfLen→reachable _ _ start⟶v in
    let path' = subst (reachable start) (sym srce≡v) path in
    subst (reachable start) deste≡end (cons e path')

  BoundedWalk→reachable : ∀ start end → BoundedWalk start end → reachable start end
  BoundedWalk→reachable start end (_ , walk) = WalkOfLen→reachable _ _ walk

  reachable→WalkOfLen : ∀ start end → reachable start end → Σ[ n ∈ ℕ ] WalkOfLen n start end
  reachable→WalkOfLen start .start nil = 0 , refl
  reachable→WalkOfLen start .(dst e) (cons e path) =
    let (n , walk) = reachable→WalkOfLen _ _ path in
    suc n , dst e , {!dst e , ?!} , {!!}

  reachable→BoundedWalk : ∀ start end → reachable start end → BoundedWalk start end
  reachable→BoundedWalk = {!!}

  ∥reachable∥≃∥BoundedWalk∥ : ∀ start end → ∥ reachable start end ∥₁ ≃ ∥ BoundedWalk start end ∥₁
  ∥reachable∥≃∥BoundedWalk∥ start end = propBiimpl→Equiv isPropPropTrunc isPropPropTrunc
                                        (PT.map $ reachable→BoundedWalk start end)
                                        (PT.map $ BoundedWalk→reachable start end)

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
