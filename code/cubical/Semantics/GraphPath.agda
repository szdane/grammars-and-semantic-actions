{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Semantics.GraphPath where

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
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Semantics.Helper
private
  variable
    ℓ ℓ' : Level

module Vec⁺ where
  open SumFin

  private variable
    n m : ℕ
    T U : Type ℓ

  data Vec⁺ (T : Type ℓ) : ℕ → Type ℓ where
    [_] : T → Vec⁺ T 0
    _∷_ : {n : ℕ} → T → Vec⁺ T n → Vec⁺ T (suc n)
  infixr 5 _∷_

  private variable
    xs ys : Vec⁺ T n

  pure : T → Vec⁺ T 0
  pure x = [ x ]

  head : Vec⁺ T n → T
  head [ x ] = x
  head (x ∷ xs) = x

  last : Vec⁺ T n → T
  last [ x ] = x
  last (x ∷ xs) = last xs

  lookup : Vec⁺ T n → Fin (suc n) → T
  lookup xs fzero = head xs
  lookup (x ∷ xs) (fsuc idx) = lookup xs idx

  tabulate : (Fin (suc n) → T) → Vec⁺ T n
  tabulate {n = 0} f = [ f fzero ]
  tabulate {n = suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

  split : (k : Fin (suc n)) → Vec⁺ T n → Vec⁺ T (toℕ k) × Vec⁺ T (n ∸ toℕ k)
  split fzero xs = [ head xs ] , xs
  split (fsuc k) (x ∷ xs) = map-fst (x ∷_) (split k xs)

  Spliceable : Vec⁺ T n → Vec⁺ T m → Type _
  Spliceable xs ys = last xs ≡ head ys

  opaque
    splice : (xs : Vec⁺ T n) (ys : Vec⁺ T m) → Spliceable xs ys → Vec⁺ T (n + m)
    splice [ l ] rs _ = rs
    splice (l ∷ ls) rs spliceable = l ∷ splice ls rs spliceable

    splice-pure : {x : T} {xs : Vec⁺ T n} {spliceable : x ≡ head xs} →
                  xs ≡ splice (pure x) xs spliceable
    splice-pure = refl

    splice-∷ : {x : T} {xs : Vec⁺ T n} {ys : Vec⁺ T m} {spliceable : Spliceable xs ys} →
                x ∷ splice xs ys spliceable ≡ splice (x ∷ xs) ys spliceable
    splice-∷ = refl

    splice-head : {spliceable : Spliceable xs ys} → head xs ≡ head (splice xs ys spliceable)
    splice-head {xs = [ x ]} {spliceable = spliceable} = spliceable
    splice-head {xs = x ∷ xs} = refl

  Split : (k : ℕ) → Vec⁺ T (k + n) → Type _
  Split {T = T} {n = n} k xs =
    Σ[ (ls , rs) ∈ Vec⁺ T k × Vec⁺ T n ] Σ[ spliceable ∈ Spliceable ls rs ]
      xs ≡ splice ls rs spliceable

  opaque
    split' : (k : ℕ) → (xs : Vec⁺ T (k + n)) → Split k xs
    split' 0 xs = (pure (head xs) , xs) , refl , splice-pure
    split' (suc k) (x ∷ xs) =
      let (xs' , spliceable , p) = split' k xs in
      map-fst (x ∷_) xs' , spliceable , congS (x ∷_) p ∙ splice-∷

  headTabulate≡ap0 : (f : Fin (suc n) → T) → head (tabulate f) ≡ f fzero
  headTabulate≡ap0 {n = 0} f = refl
  headTabulate≡ap0 {n = suc n} f = refl

  lookup-tabulate : (f : Fin (suc n) → T) (k : Fin (suc n)) → lookup (tabulate f) k ≡ f k
  lookup-tabulate f fzero = headTabulate≡ap0 f
  lookup-tabulate {n = suc n} f (fsuc k) = lookup-tabulate (f ∘ fsuc) k

  tabulate-lookup : (xs : Vec⁺ T n) → tabulate (lookup xs) ≡ xs
  tabulate-lookup [ x ] = refl
  tabulate-lookup (x ∷ xs) = congS (x ∷_) $ tabulate-lookup xs

  head≡headSplitFst : (xs : Vec⁺ T n) (k : Fin (suc n)) → head xs ≡ head (split k xs .fst)
  head≡headSplitFst xs fzero = refl
  head≡headSplitFst (x ∷ xs) (fsuc k) = refl

  opaque
    unfolding splice
    head≡headSplice : (xs : Vec⁺ T n) (ys : Vec⁺ T m) (spliceable : Spliceable xs ys) → head xs ≡ head (splice xs ys spliceable)
    head≡headSplice [ x ] ys lastxs≡headys = lastxs≡headys
    head≡headSplice (x ∷ xs) ys lastxs≡headys = refl

  module _ where
    open Iso

    Iso-Vec⁺-Finsuc→ : Iso (Vec⁺ T n) (Fin (suc n) → T)
    Iso-Vec⁺-Finsuc→ .fun = lookup
    Iso-Vec⁺-Finsuc→ .inv = tabulate
    Iso-Vec⁺-Finsuc→ .rightInv f = funExt (lookup-tabulate f)
    Iso-Vec⁺-Finsuc→ .leftInv = tabulate-lookup

    Vec⁺≃Finsuc→ : Vec⁺ T n ≃ (Fin (suc n) → T)
    Vec⁺≃Finsuc→ = isoToEquiv Iso-Vec⁺-Finsuc→

  module _ (T : FinSet ℓ) where
    isFinSetVec⁺ : isFinSet (Vec⁺ (T .fst) n)
    isFinSetVec⁺ = EquivPresIsFinSet (invEquiv Vec⁺≃Finsuc→) (isFinSet→ (_ , isFinSetFin) T)

module Between where
  open SumFin
  open Vec⁺ using (Vec⁺ ; pure ; _∷_)

  private variable
    n m : ℕ
    T U : Type ℓ
    R : T → T → Type ℓ
    x y : T
    xs ys : Vec⁺ T n

  data Between (T : Type ℓ) (R : T → T → Type ℓ') : (n : ℕ) → Vec⁺ T n → Type (ℓ-max ℓ ℓ') where
    nil : (x : T) → Between T R 0 (pure x)
    cons : R x (Vec⁺.head xs) → Between T R n xs → Between T R (suc n) (x ∷ xs)

  module _ {xs} (between : Between T R n xs) where
    headUnder = Vec⁺.head xs
    lastUnder = Vec⁺.last xs

    lookupUnder = Vec⁺.lookup xs
    lookupUnderL = lookupUnder ∘ finj
    lookupUnderR = lookupUnder ∘ fsuc

    Lookup : Fin n → Type _
    Lookup idx = R (lookupUnderL idx) (lookupUnderR idx)

  lookup : (between : Between T R n xs) (idx : Fin n) → Lookup between idx
  lookup (cons r between) fzero = r
  lookup (cons r between) (fsuc idx) = lookup between idx

  Head : Between T R (suc n) xs → Type _
  Head between = Lookup between fzero

  head : (between : Between T R (suc n) xs) → Head between
  head between = lookup between fzero

  split : (k : Fin (suc n)) → Between T R n xs → Between T R (toℕ k) (Vec⁺.split k xs .fst) × Between T R (n ∸ toℕ k) (Vec⁺.split k xs .snd)
  split fzero between = nil (headUnder between) , between
  split {R = R} (fsuc k) (cons {xs = xs} r between) = map-fst (cons (subst (R _) (Vec⁺.head≡headSplitFst xs k) r)) (split k between)

  module _
    {T : Type ℓ}
    {R : T → T → Type ℓ'}
    where opaque
    unfolding Vec⁺.splice

    splice' : {n m : ℕ} {xs : Vec⁺ T n} {ys : Vec⁺ T m}
             (spliceable : Vec⁺.Spliceable xs ys) →
             Between T R n xs → Between T R m ys →
             Between T R (n + m) (Vec⁺.splice xs ys spliceable)
    splice' spliceable (nil l) rs = rs
    splice' spliceable (cons {xs = xs} r ls) rs =
      let r' = subst (R _) Vec⁺.splice-head r in
      cons r' (splice' spliceable ls rs)

  private opaque
    cast-vec : {xs ys : Vec⁺ T n} → xs ≡ ys → Between T R n xs → Between T R n ys
    cast-vec p = subst (Between _ _ _) p

    cast-vec-filler : {xs ys : Vec⁺ T n} → (p : xs ≡ ys) → (bt : Between T R n xs) →
                      PathP (λ i → Between T R n (p i)) bt (cast-vec p bt)
    cast-vec-filler p bt = subst-filler (Between _ _ _) p bt

  module _
    {T : Type ℓ}
    {R : T → T → Type ℓ'}
    where opaque

    splice : {n m : ℕ} {xs : Vec⁺ T n} {ys : Vec⁺ T m}
             (spliceable : Vec⁺.Spliceable xs ys) →
             Between T R n xs → Between T R m ys →
             Between T R (n + m) (Vec⁺.splice xs ys spliceable)
    splice spliceable (nil l) rs = cast-vec Vec⁺.splice-pure rs
    splice spliceable (cons {xs = xs} r ls) rs =
      let r' = subst (R _) Vec⁺.splice-head r in
      cast-vec Vec⁺.splice-∷ $ cons r' (splice spliceable ls rs)

    splice-nil : {x : T} {n : ℕ} {xs : Vec⁺ T n}
                 {spliceable : Vec⁺.Spliceable (Vec⁺.pure x) xs}
                 {bt : Between T R n xs} →
                 PathP (λ i → Between T R n (Vec⁺.splice-pure {x = x} {xs} {spliceable} i))
                   bt (splice spliceable (nil x) bt)
    splice-nil = cast-vec-filler Vec⁺.splice-pure _

    splice-cons : {n m : ℕ} {xs : Vec⁺ T n} {ys : Vec⁺ T m}
                  {spliceable : Vec⁺.Spliceable xs ys}
                  {x : T} {r : R x (Vec⁺.head xs)}
                  {ls : Between T R n xs} {rs : Between T R m ys} →
                  PathP (λ i → Between T R _ (Vec⁺.splice-∷ {x = x} {xs} {ys} {spliceable} i))
                    (cons (subst (R _) Vec⁺.splice-head r) (splice spliceable ls rs))
                    (splice spliceable (cons r ls) rs)
    splice-cons = cast-vec-filler Vec⁺.splice-∷ _

  opaque
    unfolding Vec⁺.splice

    split' : (n : ℕ) {m : ℕ}
            {xs : Vec⁺ T n} {ys : Vec⁺ T m} {spliceable : Vec⁺.Spliceable xs ys} →
            (bt : Between T R (n + m) (Vec⁺.splice xs ys spliceable)) →
            Σ[ (ls , rs) ∈ Between T R n xs × Between T R m ys ] bt ≡ splice spliceable ls rs
    split' 0 {xs = Vec⁺.[ x ]} bt = (nil x , bt) , splice-nil
    split' {R = R} (suc n) {xs = x ∷ xs} {spliceable = spliceable} (cons r bt) =
      let (bt' , p) = split' n {xs = xs} {spliceable = spliceable} bt in
      map-fst (cons (subst⁻ (R _) (Vec⁺.head≡headSplice xs _ spliceable) r)) bt' , {!splice-cons!}

  Tripartition : Range n → Between T R n xs → Type _
  Tripartition {n = n} {T = T} {R = R} {xs = xs} range _ =
    let open Range range in
    let B = Between T R in
    let (ls , cs , rs) = map-snd (Vec⁺.split j') (Vec⁺.split i xs) in
    B (toℕ i) ls × B (toℕ j') cs × B (n ∸ toℕ i ∸ toℕ j') rs

  tripartition : (range : Range n) → (between : Between T R n xs) → Tripartition range between
  tripartition range between = map-snd (split j') (split i between)
    where open Range range

  -- simplify : (range : Range n) → lookup xs (range .Range.i) ≡ lookup xs (range .Range.j) → Between T R n xs → Between T R _

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

      WalkAlong : (n : ℕ) → Vec⁺ (states .fst) n → Type ℓ
      WalkAlong = Between (states .fst) (flip Adj)

      statesAlong : (walk : Walk u v) → Vec⁺ (states .fst) (length walk)
      statesAlong {u = u} nil = [ u ]
      statesAlong {v = v} (cons walk adj) = v ∷ statesAlong walk

      along : (walk : Walk u v) → WalkAlong (length walk) (statesAlong walk)
      along nil = nil _
      along (cons {u = u} nil adj) = cons adj (along nil)
      along (cons {u = u} w@(cons walk x) adj) = cons adj (along w)

      WalkAlong→Walk : (wa : WalkAlong n vs) → Walk (lastUnder wa) (headUnder wa)
      WalkAlong→Walk (nil u) = nil
      WalkAlong→Walk (cons adj wa) = cons (WalkAlong→Walk wa) adj

      length-WalkAlong→Walk : (wa : WalkAlong n vs) → length (WalkAlong→Walk wa) ≡ n
      length-WalkAlong→Walk (nil u) = refl
      length-WalkAlong→Walk (cons adj wa) = cong suc (length-WalkAlong→Walk wa)

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
