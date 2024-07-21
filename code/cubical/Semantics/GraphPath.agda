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
open import Cubical.Data.Nat.Order as Order
import      Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.NatPlusOne
import      Cubical.Data.Fin as Fin
open import Cubical.Data.SumFin as SumFin hiding (finj ; fsuc ; elim)
import      Cubical.Data.FinData as FinData
open import Cubical.Data.Vec.DepVec as DepVec'
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Semantics.Helper
private
  variable
    ℓ ℓ' : Level

-- should perhaps be in standard library, but doesn't seem to be
private
  module _ where
    open SumFin

    fin< : ∀ {n} → (k : Fin n) → toℕ k < n
    fin< {n = suc n} fzero = n , +-comm n 1
    fin< {n = suc n} (fsuc k) = fin< k .fst , +-suc _ _ ∙ congS suc (fin< k .snd)

    -- fin< : ∀ {n} → (k : Fin n) → toℕ k < n
    -- fin< {n = suc n} fzero = tt
    -- fin< {n = suc n} (fsuc k) = fin< k

module Vec where
  open SumFin

  open import Cubical.Data.Vec hiding (lookup) public

  private variable
    n : ℕ
    T U : Type ℓ

  pure : {T : Type ℓ} → T → Vec T 1
  pure x = x ∷ []

  -- There is a similar function defined in Vec, but using another definition of Fin
  lookup : Vec T n → Fin n → T
  lookup (x ∷ xs) fzero = x
  lookup (x ∷ xs) (fsuc idx) = lookup xs idx

  foldl : (U → T → U) → U → Vec T n → U
  foldl f acc [] = acc
  foldl f acc (x ∷ xs) = foldl f (f acc x) xs

  take : (k : Fin (suc n)) → Vec T n → Vec T (toℕ k)
  take fzero xs = []
  take (fsuc k) (x ∷ xs) = x ∷ take k xs

  drop : (k : Fin (suc n)) → Vec T n → Vec T (n ∸ toℕ k)
  drop fzero xs = xs
  drop (fsuc k) (x ∷ xs) = drop k xs

open Vec using (Vec ; [] )

module VecSyntax where
  infixr 5 _∷_
  _∷_ : ∀ {T : Type ℓ} {n} → T → Vec T n → Vec T (suc n)
  _∷_ = Vec._∷_
  pure = Vec.pure
  _<$>_ = Vec.map

module Vec⁺ where
  open SumFin

  private variable
    n m : ℕ
    T U : Type ℓ

  data Vec⁺ (T : Type ℓ) : ℕ → Type ℓ where
    [_] : T → Vec⁺ T 0
    _∷_ : {n : ℕ} → T → Vec⁺ T n → Vec⁺ T (suc n)
  infixr 5 _∷_

  pure : T → Vec⁺ T 0
  pure x = [ x ]

  head : Vec⁺ T n → T
  head [ x ] = x
  head (x ∷ xs) = x

  tail : Vec⁺ T n → Vec T n
  tail [ x ] = Vec.[]
  tail (x ∷ xs) = Vec._∷_ x (tail xs)

  last : Vec⁺ T n → T
  last [ x ] = x
  last (x ∷ xs) = last xs

  lookup : Vec⁺ T n → Fin (suc n) → T
  lookup xs fzero = head xs
  lookup (x ∷ xs) (fsuc idx) = lookup xs idx

  take : (k : Fin (suc n)) → Vec⁺ T n → Vec⁺ T (toℕ k)
  take fzero xs = [ head xs ]
  take (fsuc k) (x ∷ xs) = x ∷ take k xs

  drop : (k : Fin (suc n)) → Vec⁺ T n → Vec⁺ T (n ∸ toℕ k)
  drop fzero xs = xs
  drop (fsuc k) (x ∷ xs) = drop k xs

  splice : Vec⁺ T n → Vec⁺ T m → Vec⁺ T (n + m)
  splice [ l ] rs = rs
  splice (l ∷ ls) rs = l ∷ splice ls rs

  loop : (i j : Fin (suc n)) → Vec⁺ T n → Vec⁺ T (toℕ i + (n ∸ toℕ j))
  loop i j xs = splice (take i xs) (drop j xs)

  head≡headTake : (xs : Vec⁺ T n) (k : Fin (suc n)) → head xs ≡ head (take k xs)
  head≡headTake xs fzero = refl
  head≡headTake (x ∷ xs) (fsuc k) = refl

  lookup≡lastTake : (xs : Vec⁺ T n) (k : Fin (suc n)) → lookup xs k ≡ last (take k xs)
  lookup≡lastTake xs fzero = refl
  lookup≡lastTake (x ∷ xs) (fsuc k) = lookup≡lastTake xs k

  lookup≡headDrop : (xs : Vec⁺ T n) (k : Fin (suc n)) → lookup xs k ≡ head (drop k xs)
  lookup≡headDrop xs fzero = refl
  lookup≡headDrop (x ∷ xs) (fsuc k) = lookup≡headDrop xs k

  head≡headSplice : (xs : Vec⁺ T n) (ys : Vec⁺ T m) (lastxs≡headys : last xs ≡ head ys) → head xs ≡ head (splice xs ys)
  head≡headSplice [ x ] ys lastxs≡headys = lastxs≡headys
  head≡headSplice (x ∷ xs) ys lastxs≡headys = refl

module list where
  open import Cubical.Data.List

  private variable
    n m : ℕ
    T U : Type ℓ

  loop : (i j : ℕ) → List T → List T
  loop i j xs = take i xs ++ drop j xs

  x : List ℕ
  x = 0 ∷ 1 ∷ 2 ∷ 1 ∷ 4 ∷ []

  _ : loop 1 3 x ≡ 0 ∷ 1 ∷ 4 ∷ []
  _ = refl

  decomp2 : (i : ℕ) → List T → List T × List T
  decomp2 i xs = take i xs , drop i xs

  decomp2→id : (i : ℕ) (xs : List T) → take i xs ++ drop i xs ≡ xs
  decomp2→id zero xs = refl
  decomp2→id (suc i) [] = refl
  decomp2→id (suc i) (x ∷ xs) = congS (x ∷_) $ decomp2→id i xs

  decomp : (i j : ℕ) → List T → (List T × List T × List T)
  decomp i j xs = take i xs , drop i (take j xs) , drop j xs

  _ : decomp 1 3 x ≡ (0 ∷ [] , 1 ∷ 2 ∷ [] , 1 ∷ 4 ∷ [])
  _ = refl

  decomp→loop : (i j : ℕ) → (xs : List T) → decomp i j xs .fst ++ decomp i j xs .snd .snd ≡ loop i j xs
  decomp→loop i j xs = refl

  decomp→take : (i j : ℕ) → i < j → (xs : List T) → take i xs ++ drop i (take j xs) ≡ take j xs
  decomp→take i j i<j xs = {!take++!}

  decomp→id : (i j : ℕ) → (xs : List T) → decomp i j xs .fst ++ decomp i j xs .snd .fst ++ decomp i j xs .snd .snd ≡ xs
  decomp→id i j xs = {!!}

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

  Take : Fin (suc n) → Between T R n xs → Type _
  Take {T = T} {R = R} {xs = xs} k between = Between T R (toℕ k) (Vec⁺.take k xs)

  take : (k : Fin (suc n)) → (between : Between T R n xs) → Take k between
  take fzero between = nil (headUnder between)
  take {R = R} (fsuc k) (cons {xs = xs} r between) =
    let r' = subst (R _) (Vec⁺.head≡headTake xs k) r in
    cons r' (take k between)

  Drop : Fin (suc n) → Between T R n xs → Type _
  Drop {n = n} {T = T} {R = R} {xs = xs} k between = Between T R (n ∸ toℕ k) (Vec⁺.drop k xs)

  drop : (k : Fin (suc n)) → (between : Between T R n xs) → Drop k between
  drop fzero between = between
  drop (fsuc k) (cons r between) = drop k between

  Splice : (l : Between T R n xs) (r : Between T R m ys) → Type _
  Splice {T = T} {R = R} {n = n} {xs = xs} {m = m} {ys = ys} l r = Between T R (n + m) (Vec⁺.splice xs ys)

  splice : (ls : Between T R n xs) (rs : Between T R m ys) → lastUnder ls ≡ headUnder rs → Splice ls rs
  splice (nil l) rs lastl≡headr = rs
  splice {R = R} {ys = ys} (cons {xs = xs} r ls) rs lastl≡headr =
    let r' = subst (R _) (Vec⁺.head≡headSplice xs ys lastl≡headr) r in
    cons r' (splice ls rs lastl≡headr)

  Loop : Between T R n xs → Fin (suc n) → Fin (suc n) → Type _
  Loop {T = T} {R = R} {n = n} {xs = xs} between i j = Between T R (toℕ i + (n ∸ toℕ j)) (Vec⁺.splice (Vec⁺.take i xs) (Vec⁺.drop j xs))

  loop : (between : Between T R n xs) (i j : Fin (suc n)) → lookupUnder between i ≡ lookupUnder between j → Loop between i j
  loop {xs = xs} between i j lookupi≡lookupj = splice (take i between) (drop j between) (sym (Vec⁺.lookup≡lastTake xs i) ∙∙ lookupi≡lookupj ∙∙ Vec⁺.lookup≡headDrop xs j)

  loop-< : (between : Between T R n xs) (i j : Fin (suc n)) → toℕ i < toℕ j → toℕ i + (n ∸ toℕ j) < n
  loop-< {n = n} between i j = {!+induction!}
    -- where
    -- open <-Reasoning
    -- lemma : toℕ i + n < n + toℕ j
    -- lemma = toℕ i + n ≡<⟨ +-comm (toℕ i) n ⟩ <-k+ i<j

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

      opaque
        statesPhp : (walk : Walk u v) → bound < length walk → Σ[ i ∈ _ ] Σ[ j ∈ _ ] (toℕ i < toℕ j) × (Vec⁺.lookup (statesAlong walk) i ≡ Vec⁺.lookup (statesAlong walk) j)
        statesPhp walk bound<len = {!!}

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
