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
open import Cubical.Data.Sum as Sum hiding (elim ; rec)
open import Cubical.Data.Bool hiding (_⊕_ ; elim)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥ hiding (elim ; rec)
open import Cubical.Data.Unit
open import Cubical.Data.Maybe hiding (elim ; rec)
open import Cubical.Data.Nat as Nat hiding (elim)
open import Cubical.Data.Nat.Order.Recursive as Ord renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.SumFin as SumFin hiding (fsuc ; elim)
open import Cubical.Data.Vec as Vec renaming (_++_ to _++Vec_) hiding (lookup)
open import Cubical.Data.Vec.DepVec
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec)

open import Semantics.Helper
private
  variable
    ℓ ℓ' : Level

private
  -- There is a similar function defined in Vec, but using another definition of Fin
  lookup : ∀ {n} {T : Type ℓ} → Vec T n → Fin n → T
  lookup (x ∷ xs) SumFin.fzero      = x
  lookup (x ∷ xs) (SumFin.fsuc idx) = lookup xs idx

  foldlVec : ∀ {n} {T : Type ℓ} {U : Type ℓ'} → (U → T → U) → U → Vec T n → U
  foldlVec f acc [] = acc
  foldlVec f acc (x ∷ xs) = foldlVec f (f acc x) xs

record directedGraph : Type (ℓ-suc ℓ) where
  field
    states : FinSet ℓ
    directed-edges : FinSet ℓ
    src : directed-edges .fst → states .fst
    dst : directed-edges .fst → states .fst

  Adj : states .fst → states .fst → Type ℓ
  Adj u v = Σ[ e ∈ directed-edges .fst ] (src e ≡ u) × (dst e ≡ v)

  AdjIsFinSet : ∀ {u v} → isFinSet (Adj u v)
  AdjIsFinSet = isFinSetΣ directed-edges λ _ → _ ,
                    isFinSet× (_ , isFinSet≡ states _ _) (_ , isFinSet≡ states _ _)

  module Connectivity where
    -- paths approach: define Path as isFinOrd (something), write function to path, show paths are bounded

    module Walk[] where

      -- Graph walks indexed by length
      data Walk[_][_,_] : ℕ → states .fst → states .fst → Type ℓ where
        nil : ∀ {u v} → u ≡ v → Walk[ 0 ][ u , v ]
        cons : ∀ {n u v w} → Walk[ n ][ u , v ] → Adj v w → Walk[ suc n ][ u , w ]

      foldl : ∀ {u} (B : ℕ → Type ℓ')
            → (∀ {n} → B n → (v : states .fst) → B (suc n))
            → B 0
            → ∀ {n v} → Walk[ n ][ u , v ] → B n
      foldl B induct acc (nil _) = acc
      foldl B induct acc {v = v} (cons walk adj) = foldl (B ∘ suc) induct (induct acc v) walk

      module test where
        -- open import Cubical.Data.FinData as FinData using (FinVec)
        -- open import Cubical.Data.FinData.DepFinVec

        -- statesAlong : ∀ {u n v} → Walk[ n ][ u , v ] → FinVec (states .fst) (suc n)
        -- statesAlong {v = v} (nil x) fn = v
        -- statesAlong (cons walk x) fn with fn
        -- ... | FinData

        statesAlong : ∀ {u n v} → Walk[ n ][ u , v ] → Fin (suc n) → states .fst
        statesAlong {v = v} (nil _) SumFin.fzero = v
        statesAlong {v = v} (cons walk x) fn = {!fn!}

      statesAlong : ∀ {u n v} → Walk[ n ][ u , v ] → Vec (states .fst) (suc n)
      statesAlong {u} = foldl (Vec (states .fst) ∘ suc) (λ rest v → v ∷ rest) (u ∷ [])

      stateAt : ∀ {n u v} → Walk[ n ][ u , v ] → Fin (suc n) → states .fst
      stateAt walk = lookup (statesAlong walk)

      startAt0 : ∀ {n u v} → (walk : Walk[ n ][ u , v ]) → stateAt walk SumFin.fzero ≡ u
      startAt0 walk = {!!}

      prefixes : ∀ {n u v} → (walk : Walk[ n ][ u , v ]) → depVec (λ k → Walk[ k ][ u , stateAt walk (fromℕ k) ]) (suc n)
      prefixes (nil _) = (nil refl) □ ⋆
      prefixes {u = u} {w} (cons {v = v} walk adj) = (cons walk {!adj!}) □ {!prefixes walk!}
    --   opaque
    --     Walk[_] : ℕ → states .fst → states .fst → Type ℓ
    --     Walk[ 0 ]     start end = start ≡ end
    --     Walk[ suc n ] start end = Σ[ v ∈ states .fst ] Σ[ walk ∈ Walk[ n ] start v ] Adj v end

    --     Walk[]IsFinSet : ∀ {n start end} → isFinSet (Walk[ n ] start end)
    --     Walk[]IsFinSet {0}     = isFinSet≡ states _ _
    --     Walk[]IsFinSet {suc n} = isFinSetΣ states λ _ → _ ,
    --                             isFinSetΣ (_ , Walk[]IsFinSet) λ _ → _ ,
    --                             AdjIsFinSet

    --     nil : ∀ {start end} → start ≡ end → Walk[ 0 ] start end
    --     nil p = p

    --     cons : ∀ {n start v end} → Walk[ n ] start v → Adj v end → Walk[ suc n ] start end
    --     cons walk adj = _ , walk , adj

    --     _++_ : ∀ {m n start v end} → Walk[ m ] start v → Walk[ n ] v end → Walk[ m + n ] start end
    --     _++_ {n = 0} l r = subst2 (λ k → Walk[ k ] _) (sym $ +-zero _) r l
    --     _++_ {n = suc n} {start = start} {end = end} l (u , walk[n] , adj) =
    --       let walk = cons (l ++ walk[n]) adj in
    --       subst (λ k → Walk[ k ] start end) (sym $ +-suc _ _) walk
    --     infixr 5 _++_

    --     elim : {B : ∀ n start end → Walk[ n ] start end → Type ℓ'}
    --         → (∀ start end → (p : start ≡ end) → B _ _ _ (nil p))
    --         → (∀ n start end v → (walk[n] : Walk[ n ] start v) → (adj : Adj v end) → B _ _ _ walk[n] → B _ _ _ (cons walk[n] adj))
    --         → ∀ n start end → (walk[n] : Walk[ n ] start end) → B _ _ _ walk[n]
    --     elim base induct 0 _ _ p = base _ _ p
    --     elim base induct (suc n) _ _ (v , walk[n] , adj) = induct _ _ _ v walk[n] adj $ elim base induct _ _ _ walk[n]

    --     rec[] : {B : ℕ → Type ℓ'}
    --           → ((start end : states .fst) → start ≡ end → B 0)
    --           → (∀ n start end v → Walk[ n ] start v → Adj v end → B n → B (suc n))
    --           → ∀ n start end → Walk[ n ] start end → B n
    --     rec[] = elim

    --     rec : {B : Type ℓ'}
    --         → ((start end : states .fst) → start ≡ end → B)
    --         → (∀ n start end v → Walk[ n ] start v → Adj v end → B → B)
    --         → ∀ n start end → Walk[ n ] start end → B
    --     rec = rec[]

    --   module _ {n} {start} {end} (walk : Walk[ n ] start end) where
    --     statesAlong : Vec (states .fst) (suc n)
    --     statesAlong = rec[] (λ start _ _ → start ∷ [])
    --                         (λ n _ _ v _ _ states → _∷_ {n = suc n} v states)
    --                         _ _ _ walk

    --     stateAt : Fin (suc n) → states .fst
    --     stateAt = lookup statesAlong

    --     prefixes' : depVec (λ k → Walk[ k ] start (stateAt (fromℕ k))) (suc n)
    --     prefixes' = elim {B = λ n _ _ _ → depVec {!λ k → Walk[ k ] _ (stateAt (fromℕ k))!} (suc n)} (λ _ _ p → nil p □ ⋆) (λ _ _ _ v walk[n] adj → {!!} □_) _ _ _ walk

    --     prefixes : depVec (λ k → Σ[ v ∈ (states .fst)] Walk[ k ] start v) (suc n)
    --     prefixes = elim {B = λ n start end _ → depVec (λ k → Σ[ v ∈ (states .fst)] Walk[ k ] start v) (suc n)}
    --                     (λ _ _ p → (_ , nil p) □ ⋆)
    --                     (λ _ _ _ v walk[n] adj prev → (_ , cons walk[n] adj) □ prev)
    --                     _ _ _ walk

    --   simplifyLoops : ∀ {n start end} → Walk[ n ] start end → Σ[ k ∈ Fin (card states) ] Walk[ toℕ k ] start end
    --   simplifyLoops walk[n] = {!!}
    -- open Walk[] public using (Walk[_] ; Walk[]IsFinSet)

    -- module Walk where opaque
    --   -- Graph walks of arbitrary length
    --   Walk : states .fst → states .fst → Type ℓ
    --   Walk start end = Σ[ n ∈ ℕ ] Walk[ n ] start end

    --   Walk[]→Walk : ∀ {n start end} → Walk[ n ] start end → Walk start end
    --   Walk[]→Walk walk[] = _ , walk[]

    --   rec : {T : Type ℓ'}
    --       → (f : ∀ {n begin end} → Walk[ n ] begin end → T)
    --       → ∀ {begin end} → Walk begin end → T
    --   rec f (_ , walk[]) = f walk[]
    -- open Walk public hiding (rec)

    -- opaque
    --   -- Mere existence of a path between states
    --   isReachable : states .fst → states .fst → Type ℓ
    --   isReachable start end = ∥ Walk start end ∥₁

    -- -- Decidability of reachability
    -- module DecReachability where opaque
    --   bound : ℕ
    --   bound = card states

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
