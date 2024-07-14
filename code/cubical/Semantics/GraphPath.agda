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
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat as Nat
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

  adjacent : states .fst → states .fst → Type ℓ
  adjacent u v = Σ[ e ∈ directed-edges .fst ] (src e ≡ u) × (dst e ≡ v)

  adjacentIsFinSet : ∀ {u v} → isFinSet (adjacent u v)
  adjacentIsFinSet = isFinSetΣ directed-edges λ _ → _ ,
                     isFinSet× (_ , isFinSet≡ states _ _) (_ , isFinSet≡ states _ _)

  opaque
    nil' : ∀ {start end} → start ≡ end → reachable start end
    nil' start≡end = subst (reachable _) start≡end nil

    nil'-filler : ∀ {start end} (p : start ≡ end) → PathP (λ i → reachable start (p i)) nil (nil' p)
    nil'-filler p = subst-filler (reachable _) p nil

  opaque
    cons' : ∀ {start v end} → adjacent v end → reachable start v → reachable start end
    cons' {start = start} (e , srce≡v , dste≡end) path =
      let path' = subst (reachable start) (sym srce≡v) path in
      let consPath = cons e path' in
      subst (reachable start) dste≡end consPath

  opaque
    cons'' : ∀ {start v end} → ((e , srce≡v , dste≡end) : adjacent v end) → reachable start v → reachable start (dst e)
    cons'' (e , srce≡v , dste≡end) path = cons e (subst (reachable _) (sym srce≡v) path)

  -- length : ∀ {start end} → reachable start end → ℕ
  -- -- length nil = 0
  -- -- length (cons _ path) = suc (length path)
  -- length {start = start} {end = .start} nil = 0
  -- length {start = start} {end = .(dst e)} (cons e path) = suc (length {start} {src e} path)

  -- lengthNil'≡0 : ∀ {start end} (start≡end : start ≡ end) → length (nil' start≡end) ≡ 0
  -- lengthNil'≡0 {start = start} _ = refl {x = length {start = start} nil}

  -- lengthCons' : ∀ {start v end} (adj : adjacent v end) (path : reachable start v) →
  --   length (
  --     let (e , srce≡v , dste≡end) = adj in
  --     let path' = subst (reachable start) (sym srce≡v) path in
  --     let consPath = cons e path' in
  --     subst (reachable start) dste≡end consPath
  --   ) ≡ suc (length path)
  -- lengthCons' {start = start} {v} {end} adj path = {!!}

  -- Graph walks indexed by length
  Walk[_] : ℕ → states .fst → states .fst → Type ℓ
  Walk[ 0 ]     start end = start ≡ end
  Walk[ suc n ] start end = Σ[ v ∈ states .fst ] Σ[ walk ∈ Walk[ n ] start v ] adjacent v end

  -- Graph walks of arbitrary length
  Walk : states .fst → states .fst → Type ℓ
  Walk start end = Σ[ n ∈ ℕ ] Walk[ n ] start end

  -- "Efficient" graph walks, with length less than the number of vertices
  -- The idea is that any walk is equivalent to one of these
  FastWalk : states .fst → states .fst → Type ℓ
  FastWalk start end = Σ[ n ∈ Fin (card states) ] Walk[ toℕ n ] start end

  -- `Walk` is supposed to be a more convenient formulation of `reachable`,
  -- so we expect them to be equivalent
  module Conv where
    -- Walk[_]→fiberLength : ∀ n {start end} → Walk[ n ] start end → fiber (length {start = start} {end = end}) n
    -- Walk[ 0 ]→fiberLength {start = start} start≡end = nil' start≡end , refl {x = length {start = start} nil}
    -- Walk[ suc n ]→fiberLength (v , walk , adj) = cons' adj path , {!!}
    --   where
    --   path = Walk[ n ]→fiberLength walk .fst
    --   inFiber = Walk[ n ]→fiberLength walk .snd

    Walk[_]→reachable : ∀ n {start end} → Walk[ n ] start end → reachable start end
    Walk[ 0 ]→reachable = nil'
    Walk[ suc n ]→reachable (v , walk' , adj) = cons' adj (Walk[ n ]→reachable walk')

    Walk→reachable : ∀ {start end} → Walk start end → reachable start end
    Walk→reachable (n , walk) = Walk[ n ]→reachable walk

    reachable→Walk : ∀ {start end} → reachable start end → Walk start end
    reachable→Walk nil = 0 , refl
    reachable→Walk (cons e path) =
      let (n , walk') = reachable→Walk path in
      suc n , src e , walk' , e , refl , refl

    opaque
      unfolding cons'
      sec : ∀ {start end} → section (Walk→reachable {start = start} {end}) reachable→Walk
      sec nil = sym $ nil'-filler refl
      sec (cons e path) = substRefl {B = reachable _} _ ∙ congS (cons e) (substRefl {B = reachable _} _ ∙ sec path)

    isPropStates≡ : {v : states .fst} → isProp (v ≡ v)
    isPropStates≡ = isFinSet→isSet (states .snd) _ _

    contrFibers : ∀ {start end} (path : reachable start end) → isContr (fiber Walk→reachable path)
    contrFibers path .fst = reachable→Walk path , sec path
    contrFibers nil .snd (walk , isInFiber) = {!!}
    contrFibers (cons e path) .snd ((n , walk[n]) , isInFiber) = {!!}

    -- opaque
    --   unfolding nil'
    --   ret0 : ∀ {start end} (p : start ≡ end) → reachable→Walk {start = start} {end} (Walk→reachable (0 , p)) ≡ (0 , p)
    --   ret0 p with nil' p -- with abstraction satiates the positivity checker
    --   ...       | nil         = ΣPathP (refl , isFinSet→isSet (states .snd) _ _ _ p)
    --   ...       | cons e path = ΣPathP (refl , isFinSet→isSet (states .snd) _ _ _ p)

    -- opaque
    --   --unfolding cons'
    --   retsuc : ∀ {start end} n v (walk[n] : Walk[ n ] start v) (adj : adjacent v end)
    --          → reachable→Walk {start = start} {end} (Walk→reachable (suc n , v , walk[n] , adj)) ≡ (suc n , v , walk[n] , adj)
    --   retsuc n v walk[n] adj with cons' adj (Walk[ n ]→reachable walk[n])
    --   retsuc {start = start} {end} n v walk[n] (e , l , r) | path with src e | l
    --   ...                                                            | v     | refl = ?

    -- opaque
    --   unfolding nil'
    --   unfolding cons'
    --   ret : ∀ {start end} → retract (Walk→reachable {start = start} {end}) reachable→Walk
    --   ret (0 , start≡end) = ret0 start≡end
    --   ret (suc n , v , walk[n] , adj) with cons' adj (Walk[ n ]→reachable walk[n])
    --   ret {start = start} {.start} (suc n , v , walk[n] , e , l , r) | nil = {!!}
    --   ret {start = start} {.(dst e₁)} (suc n , v , walk[n] , e , l , r) | cons e₁ path = {!!}

    -- WalkIsoReachable : ∀ {start end} → Iso (Walk start end) (reachable start end)
    -- WalkIsoReachable .Iso.fun = Walk→reachable
    -- WalkIsoReachable .Iso.inv = reachable→Walk
    -- WalkIsoReachable .Iso.rightInv = sec
    -- WalkIsoReachable .Iso.leftInv = ret

    Walk≃reachable : ∀ {start end} → Walk start end ≃ reachable start end
    Walk≃reachable .fst = Walk→reachable
    Walk≃reachable .snd .equiv-proof = contrFibers

  Walk[_]IsFinSet : ∀ n {start end} → isFinSet (Walk[ n ] start end)
  Walk[_]IsFinSet = Nat.elim (λ {_} → isFinSet≡ states _ _)
                             (λ _ ih → isFinSetΣ states λ _ → _ ,
                                       isFinSetΣ (_ , ih) λ _ → _ ,
                                       adjacentIsFinSet)

  Walk[_]Dec : ∀ n {start end} → Dec ∥ Walk[ n ] start end ∥₁
  Walk[ n ]Dec = isFinSet→Dec∥∥ $ Walk[ n ]IsFinSet

  FastWalkIsFinSet : ∀ start end → isFinSet (FastWalk start end)
  FastWalkIsFinSet start end = isFinSetΣ (_ , isFinSetFin) λ _ → _ , Walk[ _ ]IsFinSet

  FastWalk→reachable : ∀ start end → FastWalk start end → reachable start end
  FastWalk→reachable start end (_ , walk) = Conv.Walk[ _ ]→reachable walk

  reachable→Walk[] : ∀ start end → reachable start end → Σ[ n ∈ ℕ ] Walk[ n ] start end
  reachable→Walk[] = {!!}

  reachable→FastWalk : ∀ start end → reachable start end → FastWalk start end
  reachable→FastWalk = {!!}

  ∥reachable∥≃∥FastWalk∥ : ∀ start end → ∥ reachable start end ∥₁ ≃ ∥ FastWalk start end ∥₁
  ∥reachable∥≃∥FastWalk∥ start end = propBiimpl→Equiv isPropPropTrunc isPropPropTrunc
                                        (PT.map $ reachable→FastWalk start end)
                                        (PT.map $ FastWalk→reachable start end)

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
