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
open import Cubical.Data.Sum as Sum hiding (elim ; rec ; map)
open import Cubical.Data.Bool hiding (_⊕_ ; elim ; _≤_ ; _≟_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥ hiding (elim ; rec)
open import Cubical.Data.Unit
open import Cubical.Data.Maybe hiding (elim ; rec)
open import Cubical.Data.Nat as Nat hiding (elim)
import      Cubical.Data.Nat.Order as Order
open import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.Fin as Fin using (finj)
open import Cubical.Data.SumFin as SumFin hiding (finj ; fsuc ; elim)
open import Cubical.Data.Vec.DepVec as DepVec'
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Semantics.Helper
private
  variable
    ℓ ℓ' : Level

module Vec where
  open import Cubical.Data.Vec hiding (lookup) public

  private variable
    n : ℕ
    T U : Type ℓ

  -- -- There is a similar function defined in Vec, but using another definition of Fin
  -- lookup : ∀ {n} {T : Type ℓ} → Vec T n → Fin n → T
  -- lookup (x ∷ xs) SumFin.fzero      = x
  -- lookup (x ∷ xs) (SumFin.fsuc idx) = lookup xs idx

  lookup : Vec T n → Fin.Fin n → T
  lookup [] (_ , idx<0) = ⊥.rec (Order.¬-<-zero idx<0)
  lookup (x ∷ xs) fidx with Fin.fsplit fidx
  ... | inl 0≡idx = x
  ... | inr (fidx' , sucfidx'≡idx) = lookup xs fidx'

  foldl : (U → T → U) → U → Vec T n → U
  foldl f acc [] = acc
  foldl f acc (x ∷ xs) = foldl f (f acc x) xs

  --ifoldr : (Fin.Fin n → T → U → U)

  -- elim : ∀ {n} {B : (idx : Fin.Fin n) → Type ℓ}
  --      → ({idx : Fin.Fin n} → T → B idx → B (suc (Fin.toℕ idx)))
  --      → B 0
  --      → Vec T n → B n
  -- elim induct base [] = base
  -- elim induct base (x ∷ xs) = {!induct x $ elim induct base xs!}

  take : (k : Fin.Fin (suc n)) → Vec T n → Vec T (Fin.toℕ k)
  take (k , k<1) [] = subst (Vec _) (sym $ Order.≤0→≡0 ∘ Order.predℕ-≤-predℕ $ k<1) []
  take (0 , k<sucn) (x ∷ xs) = []
  take (suc k , k<sucn) (x ∷ xs) = x ∷ take (k , Order.predℕ-≤-predℕ k<sucn) xs

open Vec using (Vec ; _∷_ ; [] )

module VecSyntax where

  pure : {T : Type ℓ} → T → Vec T 1
  pure x = x ∷ []

  _<$>_ : {T : Type ℓ} {U : Type ℓ} → (T → U) → ∀ {n} → Vec T n → Vec U n
  f <$> xs = Vec.map f xs

-- module DepVec where
--   open DepVec' public

--   map : ∀ {ℓ ℓ'} {G : (k : ℕ) → Type ℓ} → {G' : (k : ℕ) → Type ℓ'} → (∀ {n} → G n → G' n) → ∀ {n} → depVec G n → depVec G' n
--   map f ⋆ = ⋆
--   map f (x □ xs) = (f x) □ (map f xs)

--   _<$>_ : ∀ {ℓ ℓ'} {G : (k : ℕ) → Type ℓ} {G' : (k : ℕ) → Type ℓ'} → (∀ {n} → G n → G' n) → ∀ {n} → depVec G n → depVec G' n
--   f <$> xs = map f xs

--   pure : ∀ {ℓ} {G : (k : ℕ) → Type ℓ} → G 0 → depVec G 1
--   pure x = x □ ⋆

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

    module _ where
      open VecSyntax
      data WalkAlong : {n : ℕ} → Vec (states .fst) (suc n) → Type ℓ where
        nil : ∀ v → WalkAlong (pure v)

    module Walk where
      private variable
        n : ℕ
        u v : states .fst

      -- Graph walks indexed by length
      data Walk[_][_,_] : ℕ → states .fst → states .fst → Type ℓ where
        nil : ∀ {u v} → u ≡ v → Walk[ 0 ][ u , v ]
        cons : ∀ {n u v w} → Walk[ n ][ u , v ] → Adj v w → Walk[ suc n ][ u , w ]

      Walk[_,_] : states .fst → states .fst → Type ℓ
      Walk[ u , v ] = Σ[ n ∈ ℕ ] Walk[ n ][ u , v ]

      WalkLen : ℕ → Type ℓ
      WalkLen n = Σ[ u ∈ _ ] Σ[ v ∈ _ ] Walk[ n ][ u , v ]

      Walk : Type ℓ
      Walk = Σ[ u ∈ _ ] Σ[ v ∈ _ ] Walk[ u , v ]

      edgesAlong : Walk[ n ][ u , v ] → Vec (directed-edges .fst) n
      edgesAlong (nil p) = []
      edgesAlong (cons walk adj) = adj .fst ∷ edgesAlong walk

      statesAlong : Walk[ n ][ u , v ] → Vec (states .fst) (suc n)
      statesAlong {u = u} walk = u ∷ src <$> edgesAlong walk
        where open VecSyntax

      stateAtIdx : ∀ {n u v} → Walk[ n ][ u , v ] → Fin.Fin (suc n) → states .fst
      stateAtIdx walk = Vec.lookup (statesAlong walk)

      module Interleave
        (edges : Vec (directed-edges .fst) n)
        (vertices : Vec (states .fst) (suc n)) where

        edgeAt = Vec.lookup edges
        srcAt = src ∘ edgeAt
        dstAt = dst ∘ edgeAt

        vertAt = Vec.lookup vertices
        lAt = vertAt ∘ Fin.finj
        rAt = vertAt ∘ Fin.fsuc

        isCoherentEdge : Fin.Fin n → Type _
        isCoherentEdge idx = (srcAt idx ≡ lAt idx) × (dstAt idx ≡ rAt idx)

        isCoherent = ∀ idx → isCoherentEdge idx

        private
          coherence→adj : isCoherent → (idx : Fin.Fin (n ∸ 1)) → {!!} --Adj (src $ lookup idx) (dst $ lookup idx)
          coherence→adj coheres idx = {!!}

        →Walk : isCoherent → Walk
        →Walk coherence =
          let start = vertAt 0 , _ , _ , nil refl in
          let ev = Vec.zipWith (_,_) edges (Vec.tail vertices) in
          Vec.foldr (λ (e , w) (u , v , n , walk) → u , w , suc n , cons walk (e , {!!})) start ev

      takeWeak : (k : Fin.Fin (suc n)) (walk : Walk[ n ][ u , v ]) → Vec (directed-edges .fst) (Fin.toℕ k)
      takeWeak k walk = Vec.take k (edgesAlong walk)

      take' : (k : Fin.Fin (suc n)) (walk : Walk[ n ][ u , v ]) → Walk
      take' k walk = Interleave.→Walk (Vec.take k $ edgesAlong walk) (Vec.take (Fin.fsuc k) $ statesAlong walk)
        λ { (0 , 0<k) → {!!} , {!!}
          ; (suc idx , sucidx<k) → {!!}
          }

      take : ∀ {n u v} (k : Fin.Fin (suc n)) (walk : Walk[ n ][ u , v ]) → Walk[ Fin.toℕ k ][ u , stateAtIdx walk k ]
      take (k , k<1) (nil p) = {!nil p!}
      take fk (cons walk adj) = {!!}

      record Split {n u v} (walk : Walk[ n ][ u , v ]) : Type ℓ where
        field
          atIdx : Fin.Fin (suc n)

        atState : states .fst
        atState = stateAtIdx walk atIdx

        lengthl : ℕ
        lengthl = Fin.toℕ atIdx

        lengthr : ℕ
        lengthr = n ∸ Fin.toℕ atIdx

        walkl : Walk[ lengthl ][ u , atState ]
        walkl = {!!}

        walkr : Walk[ lengthr ][ atState , v ]
        walkr = {!!}

      -- Walk[_][_,_] : ℕ → states .fst → states .fst → Type ℓ
      -- Walk[ 0 ][ u , v ] = u ≡ v
      -- Walk[ suc n ][ u , v ] = Σ[ w ∈ states .fst ] Walk[ n ][ u , w ] × Adj w v

      -- pattern nil p = p
      -- pattern cons walk adj = _ , walk , adj

    open Walk public using ()

    -- simplifyStep< : ∀ {n u v} → Walk[ n ][ u , v ] → bound < n → Σ[ n' ∈ ℕ ] (Walk[ n' ][ u , v ] × (n' < n))
    -- simplifyStep< walk bound<n =
    --   let (l , r , split , l+r<n) = splitsPhp walk bound<n in
    --   (l + r) , (Splitᴰ→Walkᴰ split) , l+r<n

    -- private
    --   -- This should probably be in the standard library, but doesn't appear to be
    --   ¬≤→> : ∀ a b → ¬ (a ≤ b) → b < a
    --   ¬≤→> a b ¬a≤b with a ≟ b
    --   ... | lt a<b = ⊥.elim $ ¬a≤b (<-weaken {a} a<b)
    --   ... | eq a≡b = ⊥.elim $ ¬a≤b (subst (a ≤_) a≡b (≤-refl a))
    --   ... | gt b<a = b<a

    -- simplifyStep : ∀ {n u v} → Walk[ n ][ u , v ] → Σ[ n' ∈ ℕ ] (Walk[ n' ][ u , v ] × ((n' < n) ⊎ (n' ≤ bound)))
    -- simplifyStep {n} walk with n ≤? bound
    -- ... | yes n≤bound =
    --         n , walk , inr n≤bound
    -- ... | no ¬n≤bound =
    --         let bound<n = ¬≤→> n bound ¬n≤bound in
    --         let (l , r , split , l+r<n) = splitsPhp walk bound<n in
    --         (l + r) , (Splitᴰ→Walkᴰ split) , inl l+r<n

    -- simplify : ∀ {n u v} → WalksAreBounded n u v
    -- simplify {n} {u} {v} = wf-elim {P = λ n → WalksAreBounded n u v}
    --   (λ n ih walk →
    --     let (n' , walk' , ineq) = simplifyStep walk in
    --     Sum.rec
    --       (λ n'<n → ih n' n'<n walk')
    --       (λ n'≤bound → n' , walk' , n'≤bound)
    --       ineq
    --   ) n

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
