{-# OPTIONS -WnoUnsupportedIndexedMatch --no-require-unique-meta-solutions #-}
module Semantics.GraphPath where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum hiding (elim ; rec ; map)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥ hiding (elim ; rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat as Nat hiding (elim)
import      Cubical.Data.Nat.Order.Recursive as NatOrd
open import Cubical.Data.SumFin as SumFin hiding (finj ; fsuc ; elim)
open import Cubical.Data.SumFin.More
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

import      Cubical.Data.Vec.Nonempty as Vec⁺

open import Semantics.Helper
private
  variable
    ℓ ℓ' : Level

module Between where
  open SumFin
  open Vec⁺ using (Vec⁺ ; pure ; _∷_)

  private variable
    n m : ℕ
    T U : Type ℓ
    R : T → T → Type ℓ
    x y : T
    xs ys : Vec⁺ T n

  data Between {T : Type ℓ} (R : T → T → Type ℓ') : {n : ℕ} → Vec⁺ T n → Type (ℓ-max ℓ ℓ') where
    nil : (x : T) → Between R (pure x)
    cons : {x hd : T} {xs : Vec⁺ T n} → R x hd → hd ≡ Vec⁺.head xs → Between R xs → Between R (x ∷ xs)

  module _ {xs : Vec⁺ T n} (between : Between R xs) where
    headUnder = Vec⁺.head xs
    lastUnder = Vec⁺.last xs

    lookupUnder = Vec⁺.lookup xs
    lookupUnderL = lookupUnder ∘ finj
    lookupUnderR = lookupUnder ∘ fsuc

  module _
    {T : Type ℓ}
    {R : T → T → Type ℓ'}
    where

    open Vec⁺.Spliceable

    private BT = Between R

    splice : {n m : ℕ} (sp : Vec⁺.Spliceable T n m) →
             BT (sp .l) → BT (sp .r) → BT (spliced sp)
    splice sp (nil l) rs = rs
    splice sp (cons r p ls) rs =
      let sp' = Vec⁺.unconsl sp in
      cons r (p ∙ Vec⁺.head-spliced sp') $ splice sp' ls rs

    split : (n : ℕ) {m : ℕ} (sp : Vec⁺.Spliceable T n m)
            (bt : BT (Vec⁺.spliced sp)) →
            Σ[ (ls , rs) ∈ BT () ]

    -- split : (n : ℕ) {m : ℕ} {xs : Vec⁺ T n} {ys : Vec⁺ T m}
    --         (spliceable : Vec⁺.AreSpliceable xs ys)
    --         (bt : BT (Vec⁺.splice xs ys spliceable)) →
    --         Σ[ (ls , rs) ∈ BT xs × BT ys ] bt ≡ splice spliceable ls rs
    -- split 0 {xs = Vec⁺.[ x ]} spliceable bt = ((nil x) , bt) , refl
    -- split (suc n) {xs = x ∷ xs} spliceable (cons r p bt) =
    --   let (bt' , splice-bt') = split n spliceable bt in
    --   ( map-fst (cons r (p ∙ (sym $ Vec⁺.splice-head spliceable))) bt'
    --   , cong₂ (cons r)
    --       (Gpd.rUnit p ∙ congS (p ∙_) (sym ∘ Gpd.lCancel $ Vec⁺.splice-head spliceable) ∙ Gpd.assoc _ _ _)
    --       splice-bt')
    --   where open import Cubical.Foundations.GroupoidLaws as Gpd

    -- split' : (n : ℕ) {m : ℕ} {xs : Vec⁺ T n} {ys : Vec⁺ T m}
    --          (spliceable : Vec⁺.Spliceable xs ys)

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

    private variable
      n : ℕ
      start u v : states .fst
      vs : Vec⁺.Vec⁺ (states .fst) n

    data Walk (start : states .fst) : states .fst → Type ℓ where
      nil : Walk start start
      cons : Walk start u → Adj u v → Walk start v

    length : Walk u v → ℕ
    length nil = 0
    length (cons walk adj) = suc (length walk)

    module _ where
      open Vec⁺
      open Between

      WalkAlong : Vec⁺ (states .fst) n → Type ℓ
      WalkAlong = Between (flip Adj)

      statesAlong : (walk : Walk u v) → Vec⁺ (states .fst) (length walk)
      statesAlong {u = u} nil = [ u ]
      statesAlong {v = v} (cons walk adj) = v ∷ statesAlong walk

      -- along : (walk : Walk u v) → WalkAlong (length walk) (statesAlong walk)
      -- along nil = nil _
      -- along (cons {u = u} nil adj) = cons adj (along nil)
      -- along (cons {u = u} w@(cons walk x) adj) = cons adj (along w)

      -- WalkAlong→Walk : (wa : WalkAlong n vs) → Walk (lastUnder wa) (headUnder wa)
      -- WalkAlong→Walk (nil u) = nil
      -- WalkAlong→Walk (cons adj wa) = cons (WalkAlong→Walk wa) adj

      -- length-WalkAlong→Walk : (wa : WalkAlong n vs) → length (WalkAlong→Walk wa) ≡ n
      -- length-WalkAlong→Walk (nil u) = refl
      -- length-WalkAlong→Walk (cons adj wa) = cong suc (length-WalkAlong→Walk wa)

      bound : ℕ
      bound = card states

      -- opaque
      --   statesPhp : (walk : Walk u v) → bound < length walk → Σ[ i ∈ _ ] Σ[ j ∈ _ ] (toℕ i < toℕ j) × (Vec⁺.lookup (statesAlong walk) i ≡ Vec⁺.lookup (statesAlong walk) j)
      --   statesPhp walk bound<len = {!!}

      -- simplifyStep< : (walk : Walk u v) → bound < length walk → Σ[ walk' ∈ Walk u v ] length walk' < length walk
      -- simplifyStep< walk bound<len =
      --   let (i , j , i<j , statei≡statej) = statesPhp walk bound<len in
      --   let l = Between.take i (along walk) in
      --   let r = Between.drop j (along walk) in
      --   let alongWalk' = Between.splice l r {!statei≡statej!} in
      --   let walk' = WalkAlong→Walk alongWalk' in
      --   let j≤lenwalk : toℕ j ≤ length walk
      --       j≤lenwalk = predℕ-≤-predℕ (fin< j) in
      --   let lem : toℕ j + length walk' < toℕ j + length walk
      --       lem = toℕ j + length walk' ≡<⟨ +-comm _ _ ⟩
      --             length walk' + toℕ j ≡<⟨ congS (_+ toℕ j) $ length-WalkAlong→Walk alongWalk' ⟩
      --             (toℕ i + (length walk ∸ toℕ j)) + toℕ j ≡<⟨ +-assoc _ _ _ ⟩
      --             toℕ i + ((length walk ∸ toℕ j) + toℕ j) ≡<⟨ congS (toℕ i +_) (≤-∸-+-cancel j≤lenwalk) ⟩
      --             toℕ i + length walk <≡⟨ <-+k {k = length walk} i<j ⟩ refl in
      --   let lenwalk'<lenwalk = <-k+-cancel {k = toℕ j} lem in
      --   {!!} , {!!}
      --   where open <-Reasoning

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
