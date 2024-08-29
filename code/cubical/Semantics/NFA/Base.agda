open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.NFA.Base ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.FinSet

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Term (Σ₀ , isSetΣ₀)

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

record NFA : Type (ℓ-suc ℓN) where
  field
    Q : FinSet ℓN
    init : Q .fst
    isAcc : Q .fst → DecProp ℓN
    transition : FinSet ℓN
    src : transition .fst → Q .fst
    dst : transition .fst → Q .fst
    label : transition .fst → Σ₀
    ε-transition : FinSet ℓN
    ε-src : ε-transition .fst → Q .fst
    ε-dst : ε-transition .fst → Q .fst

  decEqQ : Discrete (Q .fst)
  decEqQ = isFinSet→Discrete (Q .snd)

  -- The grammar "Parse q" denotes the type of traces in the NFA
  -- from state q to an accepting state
  data Parse : (q : Q .fst) → Grammar ℓN where
    nil : ∀ {q} → isAcc q .fst .fst →
      ε-grammar ⊢ Parse q
    cons : ∀ tr →
      literal (label tr) ⊗ Parse (dst tr) ⊢ Parse (src tr)
    ε-cons : ∀ εtr →
      Parse (ε-dst εtr) ⊢ Parse (ε-src εtr)

  InitParse : Grammar ℓN
  InitParse = Parse init

  record Algebra : Typeω where
    field
      the-ℓs : Q .fst → Level
      G : (q : Q .fst) → Grammar (the-ℓs q)
      nil-case : ∀ {q} → isAcc q .fst .fst →
        ε-grammar ⊢ G q
      cons-case : ∀ tr →
        literal (label tr) ⊗ G (dst tr) ⊢ G (src tr)
      ε-cons-case : ∀ εtr →
        G (ε-dst εtr) ⊢ G (ε-src εtr)

  open Algebra

  initial : Algebra
  the-ℓs initial _ = ℓN
  G initial = Parse
  nil-case initial = nil
  cons-case initial = cons
  ε-cons-case initial = ε-cons

  record AlgebraHom (alg alg' : Algebra) : Typeω where
    field
      f : (q : Q .fst) → alg .G q ⊢ alg' .G q
      on-nil : ∀ {q} → (qAcc : isAcc q .fst .fst) →
        f q ∘g alg .nil-case qAcc ≡ alg' .nil-case qAcc
      on-cons : (tr : transition .fst) →
        f (src tr) ∘g alg .cons-case tr ≡
          alg' .cons-case tr ∘g (⊗-intro id (f (dst tr)))
      on-ε-cons : (εtr : ε-transition .fst) →
        (f (ε-src εtr)) ∘g (alg .ε-cons-case εtr) ≡
          alg' .ε-cons-case εtr ∘g f (ε-dst εtr)
    fInit = f init

  open AlgebraHom

  idAlgebraHom : (alg : Algebra) →
    AlgebraHom alg alg
  f (idAlgebraHom alg) q-start = id
  on-nil (idAlgebraHom alg) _ = refl
  on-cons (idAlgebraHom alg) _ = refl
  on-ε-cons (idAlgebraHom alg) _ = refl

  AlgebraHom-seq : {alg alg' alg'' : Algebra} →
    AlgebraHom alg alg' → AlgebraHom alg' alg'' →
    AlgebraHom alg alg''
  f (AlgebraHom-seq ϕ ψ) q _ x =
    ψ .f q _ (ϕ .f q _ x)
  on-nil (AlgebraHom-seq ϕ ψ) qAcc =
    cong (λ t → t ⋆ ψ .f _) (ϕ .on-nil qAcc) ∙
    ψ .on-nil qAcc
  on-cons (AlgebraHom-seq ϕ ψ) tr =
    cong (λ t → t ⋆ ψ .f (src tr)) (ϕ .on-cons tr) ∙
    cong (λ t → ⊗-intro id (ϕ .f (dst tr)) ⋆ t) (ψ .on-cons tr)
  on-ε-cons (AlgebraHom-seq ϕ ψ) εtr =
    cong (λ t → t ⋆ ψ .f (ε-src εtr)) (ϕ .on-ε-cons εtr) ∙
    cong (λ t → ϕ .f (ε-dst εtr)⋆ t) (ψ .on-ε-cons εtr)

  module _
    (the-alg : Algebra)
    where
    recTrace : ∀ {q} → Parse q ⊢ the-alg .G q
    recTrace _ (nil qAcc _ pε) = the-alg .nil-case qAcc _ pε
    recTrace _ (cons tr _ p⊗) =
      the-alg .cons-case tr _
        ((p⊗ .fst) , ((p⊗ .snd .fst) , (recTrace _ (p⊗ .snd .snd))))
    recTrace _ (ε-cons εtr _ p) =
      the-alg .ε-cons-case εtr _ (recTrace _ p)

    recInit : Parse init ⊢ the-alg .G init
    recInit = recTrace

    ∃AlgebraHom : AlgebraHom initial the-alg
    f ∃AlgebraHom q = recTrace {q}
    on-nil ∃AlgebraHom _ = refl
    on-cons ∃AlgebraHom _ = refl
    on-ε-cons ∃AlgebraHom _ = refl

    !AlgebraHom-help :
      (e : AlgebraHom initial the-alg) →
      (q : Q .fst) →
      (∀ w p → e .f q w p ≡ recTrace w p)
    !AlgebraHom-help e q w (nil qAcc .w pε) =
      cong (λ a → a w pε) (e .on-nil qAcc)
    !AlgebraHom-help e .(src tr) w (cons tr .w p⊗) =
      cong (λ a → a w p⊗) (e .on-cons tr) ∙
      cong (λ a → the-alg .cons-case tr _
        ((p⊗ .fst) , ((p⊗ .snd .fst) , a)))
        (!AlgebraHom-help e (dst tr) _
          (p⊗ .snd .snd))
    !AlgebraHom-help e .(ε-src εtr) w (ε-cons εtr .w p) =
      cong (λ a → a w p) (e .on-ε-cons εtr) ∙
      cong (the-alg .ε-cons-case εtr w)
        (!AlgebraHom-help e (ε-dst εtr) _ p)

    !AlgebraHom :
      (e : AlgebraHom initial the-alg) →
      (q : Q .fst) →
      e .f q ≡ recTrace {q}
    !AlgebraHom e q =
      funExt (λ w → funExt (λ p → !AlgebraHom-help e q w p))

    -- TODO rename
    !AlgebraHom' :
      (e e' : AlgebraHom initial the-alg) →
      (q : Q .fst) →
      e .f q ≡ e' .f q
    !AlgebraHom' e e' q =
      !AlgebraHom e q ∙
      sym (!AlgebraHom e' q)

  initial→initial≡id :
    (e : AlgebraHom initial initial) →
    (q : Q .fst) →
    (e .f q)
       ≡
    id
  initial→initial≡id e q =
    !AlgebraHom initial e q ∙
    sym (!AlgebraHom initial (idAlgebraHom initial) q)

  algebra-η :
    (e : AlgebraHom initial initial) →
    fInit e ≡ id
  algebra-η e = initial→initial≡id e _

  -- Often it is convenient to do a recursion on something with other
  -- variables in scope. For this we develop the notion of a
  -- *parameterized* algebra, where we have an additional parameter
  -- that has to be consumed in the base case. In general we could
  -- have two parameters: a left and right parameter, but this is the
  -- only one we need so far.
  module _ {ℓp} (P : Grammar ℓp) where
    record PAlgebra : Typeω where
      field
        the-ℓs : Q .fst → Level
        G : (q : Q .fst) → Grammar (the-ℓs q)
        nil-case : ∀ {q} → isAcc q .fst .fst →
          P ⊢ G q
        cons-case : ∀ tr →
          (literal (label tr) ⊗ G (dst tr)) ⊢ G (src tr)
        ε-cons-case : ∀ εtr →
          G (ε-dst εtr) ⊢ G (ε-src εtr)

    open PAlgebra

    P-initial : PAlgebra
    P-initial .the-ℓs = _
    P-initial .G q = Parse q ⊗ P
    P-initial .nil-case acc = ⊗-intro (nil acc) id ∘g ⊗-unit-l⁻
    P-initial .cons-case tr = ⊗-intro (cons tr) id ∘g ⊗-assoc
    P-initial .ε-cons-case tr = ⊗-intro (ε-cons tr) id

    record PAlgebraHom (alg alg' : PAlgebra) : Typeω where
      field
        f : (q : Q .fst) → alg .G q ⊢ alg' .G q
        on-nil : ∀ {q} → (qAcc : isAcc q .fst .fst) →
          f q ∘g alg .nil-case qAcc ≡ alg' .nil-case qAcc
        on-cons : (tr : transition .fst) →
          f (src tr) ∘g alg .cons-case tr ≡
            alg' .cons-case tr ∘g (⊗-intro id (f (dst tr)))
        on-ε-cons : (εtr : ε-transition .fst) →
          (f (ε-src εtr)) ∘g (alg .ε-cons-case εtr) ≡
            alg' .ε-cons-case εtr ∘g f (ε-dst εtr)

    open PAlgebraHom

    P-idAlgebraHom : (alg : PAlgebra) → PAlgebraHom alg alg
    P-idAlgebraHom alg .f _ = id
    P-idAlgebraHom alg .on-nil _ = refl
    P-idAlgebraHom alg .on-cons _ = refl
    P-idAlgebraHom alg .on-ε-cons _ = refl

    PAlgebraHom-seq : {alg alg' alg'' : PAlgebra} →
      PAlgebraHom alg alg' → PAlgebraHom alg' alg'' →
      PAlgebraHom alg alg''
    PAlgebraHom-seq ϕ ψ .f q = ψ .f q ∘g ϕ .f q
    PAlgebraHom-seq ϕ ψ .on-nil qAcc =
      cong (ψ .f _ ∘g_) (ϕ .on-nil qAcc) ∙
      ψ .on-nil qAcc
    PAlgebraHom-seq ϕ ψ .on-cons t =
      cong (ψ .f (src t) ∘g_) (ϕ .on-cons t) ∙
      cong (_∘g ⊗-intro id (ϕ .f (dst t))) (ψ .on-cons t)
    PAlgebraHom-seq ϕ ψ .on-ε-cons t =
      cong (ψ .f (ε-src t) ∘g_) (ϕ .on-ε-cons t) ∙
      cong (_∘g ϕ .f (ε-dst t)) (ψ .on-ε-cons t)

    module _ (the-p-alg : PAlgebra) where
      the-alg : Algebra
      the-alg .the-ℓs = _
      the-alg .G q = (the-p-alg .G q) ⊗- P
      the-alg .nil-case qAcc =
        ⟜-intro ((the-p-alg .nil-case qAcc) ∘g ⊗-unit-l)
      the-alg .cons-case t =
         ⟜-intro ((the-p-alg .cons-case t) ∘g ⊗-intro id ⟜-app ∘g ⊗-assoc⁻)
      the-alg .ε-cons-case t =
         ⟜-intro ((the-p-alg .ε-cons-case t) ∘g ⟜-app)

      P-recTrace : ∀ {q} → Parse q ⊗ P ⊢ the-p-alg .G q
      P-recTrace = ⟜-app ∘g ⊗-intro (recTrace the-alg) id

      P-recInit : InitParse ⊗ P ⊢ the-p-alg .G init
      P-recInit = P-recTrace

      ∃PAlgebraHom : PAlgebraHom P-initial the-p-alg
      ∃PAlgebraHom .f q = P-recTrace
      ∃PAlgebraHom .on-nil qAcc =
        (λ i → ⟜-app ∘g ⊗-intro (∃AlgebraHom the-alg .on-nil qAcc i) id
          ∘g ⊗-unit-l⁻) ∙
        (λ i → ⟜-β (the-p-alg .nil-case qAcc ∘g ⊗-unit-l) i ∘g ⊗-unit-l⁻) ∙
        (λ i → the-p-alg .nil-case qAcc ∘g ⊗-unit-l⁻l i)
      ∃PAlgebraHom .on-cons t =
        {!!}
      ∃PAlgebraHom .on-ε-cons t =
        (λ i → (⟜-β (the-p-alg .ε-cons-case t ∘g ⟜-app)) i ∘g
          {!!}) ∙
        {!!}
