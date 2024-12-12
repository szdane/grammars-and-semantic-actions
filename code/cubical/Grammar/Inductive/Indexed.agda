{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Indexed (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Helper
open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

private
  variable ℓG ℓG' ℓ ℓ' ℓ'' ℓ''' : Level

module _ where
  data Functor (A : Type ℓ) : Type (ℓ-suc ℓ) where
    k : (g : Grammar ℓ) → Functor A
    Var : (a : A) → Functor A -- reference one of the mutually inductive types being defined
    &e ⊕e : ∀ (B : Type ℓ) → (F : B → Functor A) → Functor A
    ⊗e : (F : Functor A) → (F' : Functor A) → Functor A

  module _ {A : Type ℓ}{ℓ'} where
    ⟦_⟧ : Functor A → (A → Grammar ℓ') → Grammar (ℓ-max ℓ ℓ')
    ⟦ k h ⟧ g = LiftG ℓ' h
    ⟦ Var a ⟧ g = LiftG ℓ (g a)
    ⟦ &e B F ⟧ g = &[ b ∈ B ] ⟦ F b ⟧ g
    ⟦ ⊕e B F ⟧ g = ⊕[ b ∈ B ] ⟦ F b ⟧ g
    ⟦ ⊗e F F' ⟧ g = ⟦ F ⟧ g ⊗ ⟦ F' ⟧ g

  map : ∀ {A : Type ℓ}(F : Functor A) {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}
        → (∀ a → g a ⊢ h a)
        → ⟦ F ⟧ g ⊢ ⟦ F ⟧ h
  map (k g) f = liftG ∘g lowerG
  map (Var a) f = liftG ∘g f a ∘g lowerG
  map (&e B F) f = &ᴰ-intro λ a → map (F a) f ∘g &ᴰ-π a
  map (⊕e B F) f = ⊕ᴰ-elim λ a → ⊕ᴰ-in a ∘g map (F a) f
  map (⊗e F F') f = map F f ,⊗ map F' f

  module _ {A : Type ℓ} where
    opaque
      unfolding _⊗_ ⊗-intro

      map-id : ∀ (F : Functor A) {g : A → Grammar ℓ'} →
        map F (λ a → id {g = g a}) ≡ id
      map-id (k g) i = id
      map-id (Var a) i = id
      map-id (&e B F) i = &ᴰ-intro (λ a → map-id (F a) i ∘g &ᴰ-π a)
      map-id (⊕e B F) i = ⊕ᴰ-elim (λ a → ⊕ᴰ-in a ∘g map-id (F a) i)
      map-id (⊗e F F') i = map-id F i ,⊗ map-id F' i

      map-∘ :  ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}{k : A → Grammar ℓ'''}
        (F : Functor A)
        (f : ∀ a → h a  ⊢ k a)(f' : ∀ a → g a ⊢ h a)
        → map F (λ a → f a ∘g f' a) ≡ map F f ∘g map F f'
      map-∘ (k g) f f' i = liftG ∘g lowerG
      map-∘ (Var a) f f' i = liftG ∘g f a ∘g f' a ∘g lowerG
      map-∘ (&e B F) f f' i = &ᴰ-intro (λ a → map-∘ (F a) f f' i ∘g &ᴰ-π a)
      map-∘ (⊕e B F) f f' i = ⊕ᴰ-elim (λ a → ⊕ᴰ-in a ∘g map-∘ (F a) f f' i)
      map-∘ (⊗e F F') f f' i = map-∘ F f f' i ,⊗ map-∘ F' f f' i

    -- NOTE: this is only needed because ⊗ is opaque. If it's not
    -- opaque this passes the positivity check.
    -- https://github.com/agda/agda/issues/6970
    {-# NO_POSITIVITY_CHECK #-}
    data μ (F : A → Functor A) a : Grammar ℓ where
      roll : ⟦ F a ⟧ (μ F) ⊢ μ F a

  module _ {A : Type ℓ} (F : A → Functor A) where
    Algebra : (A → Grammar ℓ') → Type (ℓ-max ℓ ℓ')
    Algebra g = ∀ a → ⟦ F a ⟧ g ⊢ g a

    initialAlgebra : Algebra (μ F)
    initialAlgebra = λ a → roll

    Homomorphism : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''} → Algebra g → Algebra h → Type _
    Homomorphism {g = g}{h} α β =
      Σ[ ϕ ∈ (∀ a → g a ⊢ h a) ]
      (∀ a → ϕ a ∘g α a ≡ β a ∘g map (F a) ϕ)

    idHomo : ∀ {g : A → Grammar ℓ'} → (α : Algebra g) → Homomorphism α α
    idHomo α = (λ a → id) , λ a → cong (α a ∘g_) (sym (map-id (F a)))

    compHomo : ∀ {g : A → Grammar ℓ'}{h : A → Grammar ℓ''}{k : A → Grammar ℓ'''}
      (α : Algebra g)(β : Algebra h)(η : Algebra k)
      → Homomorphism β η → Homomorphism α β → Homomorphism α η
    compHomo α β η ϕ ψ .fst a = ϕ .fst a ∘g ψ .fst a
    compHomo α β η ϕ ψ .snd a =
      cong (ϕ .fst a ∘g_) (ψ .snd a)
      ∙ cong (_∘g map (F a) (ψ .fst)) (ϕ .snd a)
      ∙ cong (η a ∘g_) (sym (map-∘ (F a) (ϕ .fst) (ψ .fst)))

    module _ {g : A → Grammar ℓ'} (α : Algebra g) where
      {-# TERMINATING #-}
      recHomo : Homomorphism initialAlgebra α
      recHomo .fst a w (roll ._ x) =
        α a w (map (F a) (recHomo .fst) w x)
      recHomo .snd a = refl

      rec : ∀ a → (μ F a) ⊢ g a
      rec = recHomo .fst

      module _ (ϕ : Homomorphism initialAlgebra α) where
        private
          {-# TERMINATING #-}
          μ-η' : ∀ a w x → ϕ .fst a w x ≡ rec a w x
          μ-η' a w (roll _ x) =
            (λ i → ϕ .snd a i w x)
            ∙ λ i → α a w (map (F a) (λ a w x → μ-η' a w x i) w x)
        μ-η : ϕ .fst ≡ rec
        μ-η = funExt (λ a → funExt λ w → funExt λ x → μ-η' a w x)

      ind : (ϕ ϕ' : Homomorphism initialAlgebra α) → ϕ .fst ≡ ϕ' .fst
      ind ϕ ϕ' = μ-η ϕ ∙ sym (μ-η ϕ')

      ind' : ∀ (ϕ ϕ' : Homomorphism initialAlgebra α) → ∀ a → ϕ .fst a ≡ ϕ' .fst a
      ind' ϕ ϕ' = funExt⁻ (ind ϕ ϕ')

    ind-id : ∀ (ϕ : Homomorphism initialAlgebra initialAlgebra) → ϕ .fst ≡ idHomo initialAlgebra .fst
    ind-id ϕ = ind initialAlgebra ϕ (idHomo initialAlgebra)

    ind-id' : ∀ (ϕ : Homomorphism initialAlgebra initialAlgebra) a → ϕ .fst a ≡ id
    ind-id' ϕ a = funExt⁻ (ind-id ϕ) a

    unroll : ∀ a → μ F a ⊢ ⟦ F a ⟧ (μ F)
    unroll a w (roll .w x) = x

    -- Lambek's lemma for indexed inductives
    unroll' : ∀ a → μ F a ⊢ ⟦ F a ⟧ (μ F)
    unroll' = rec {g = λ a → ⟦ F a ⟧ (μ F)} alg where
      alg : Algebra (λ a → ⟦ F a ⟧ (μ F))
      alg a = map (F a) (λ _ → roll)

module _ (A : Type ℓ) {ℓ'} where
  LiftFunctor : (F : Functor A) → Functor (Lift {j = ℓ'} A)
  LiftFunctor (k g) = k (LiftG ℓ' g)
  LiftFunctor (Var a) = Var (lift a)
  LiftFunctor (&e B F) = &e (Lift {j = ℓ'} B) (λ b → LiftFunctor (F (lower b)))
  LiftFunctor (⊕e B F) = ⊕e (Lift {j = ℓ'} B) (λ b → LiftFunctor (F (lower b)))
  LiftFunctor (⊗e F F₁) = ⊗e (LiftFunctor F) (LiftFunctor F₁)

  lowerFunctor :
    {ℓ''' : Level} →
    (F : Functor A) → {g : A → Grammar ℓ''}
    → ⟦ LiftFunctor F ⟧ (λ (lift a) → LiftG ℓ''' (g a)) ⊢ ⟦ F ⟧ g
  lowerFunctor (k g) = liftG ∘g lowerG ∘g lowerG
  lowerFunctor (Var a) = liftG ∘g lowerG ∘g lowerG
  lowerFunctor (&e B F) = &ᴰ-in (λ b → lowerFunctor (F b) ∘g &ᴰ-π (lift b))
  lowerFunctor (⊕e B F) = ⊕ᴰ-elim (λ (lift b) → ⊕ᴰ-in b ∘g lowerFunctor (F b))
  lowerFunctor (⊗e F F₁) = lowerFunctor F ,⊗ lowerFunctor F₁

  liftFunctor :
    {ℓ''' : Level} →
    (F : Functor A) → {g : A → Grammar ℓ''}
    → ⟦ F ⟧ g ⊢ ⟦ LiftFunctor F ⟧ (λ (lift a) → LiftG ℓ''' (g a))
  liftFunctor (k g) = liftG ∘g liftG ∘g lowerG
  liftFunctor (Var a) = liftG ∘g liftG ∘g lowerG
  liftFunctor (&e B F) = &ᴰ-in (λ (lift b) → liftFunctor (F b) ∘g &ᴰ-π b)
  liftFunctor (⊕e B F) = ⊕ᴰ-elim (λ b → ⊕ᴰ-in (lift b) ∘g liftFunctor (F b))
  liftFunctor (⊗e F F₁) = liftFunctor F ,⊗ liftFunctor F₁

  module _ {F : A → Functor A} where
    private
      A' = Lift {j = ℓ'} A

      F' : A' → Functor A'
      F' (lift a) = LiftFunctor (F a)

    module _ {g : A → Grammar ℓ''} where
      private
        L = ℓ-max ℓ'' (ℓ-max ℓ ℓ')

        g' : A' → Grammar L
        g' (lift a) = LiftG (ℓ-max ℓ ℓ') (g a)

      module _ (the-alg : Algebra F g) where
        LiftAlg : Algebra F' g'
        LiftAlg (lift a) = liftG ∘g the-alg a ∘g lowerFunctor (F a)
      module _ (the-alg : Algebra F' g') where
        LowerAlg : Algebra F g
        LowerAlg a = lowerG ∘g the-alg (lift a) ∘g liftFunctor (F a)

    module _ {a : A} where
      lowerF : μ F' (lift a) ⊢ μ F a
      lowerF =
        rec _
          (λ (lift a') →
            roll
            ∘g lowerFunctor {ℓ''' = ℓ-max ℓ ℓ'} (F a')
            ∘g map (F' (lift a')) (λ _ → liftG))
          (lift a)

      liftF : μ F a ⊢ μ F' (lift a)
      liftF =
        rec _
          (λ a' →
            roll
            ∘g map (F' (lift a')) (λ _ → lowerG)
            ∘g liftFunctor {ℓ''' = ℓ-max ℓ ℓ'} (F a'))
          a
