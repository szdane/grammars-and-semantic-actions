open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Prelude.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

module Grammar.Inductive.HLevels (Alphabet : hSet ℓ-zero)where

open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.W.Indexed

open import Helper
open import Grammar.Base Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet as Inductive
open import Grammar.Inductive.LiftFunctor Alphabet
open import Term.Base Alphabet

private
  variable ℓA ℓB ℓX ℓY ℓ : Level

isSetValued : ∀ {X : Type ℓX} → Functor X ℓ → Type (ℓ-max ℓ ℓX)
isSetValued {ℓX = ℓX} (k A) = isSetGrammar (LiftG ℓX A)
isSetValued {X = X} (Var x) = Unit*
isSetValued (&e Y F) = ∀ y → isSetValued (F y)
isSetValued (⊕e Y F) = isSet Y × (∀ y → isSetValued (F y))
isSetValued (⊗e F G) = isSetValued F × isSetValued G

module _ {X : Type ℓX} where
  FS : (F : Functor X ℓ) → String → Type (ℓ-max ℓ ℓX)
  FS {ℓ = ℓ} F = ⟦ F ⟧ λ x w → Unit* {ℓX}
  opaque
    unfolding _⊗_

    FP : (F : Functor X ℓ) → (w : String) → FS F w → Type (ℓ-max ℓ ℓX)
    FP (k A) w s = ⊥*
    FP (Var x) w s = Unit*
    FP (&e Y F) w s = Σ[ y ∈ Y ] FP (F y) w (s y)
    FP (⊕e Y F) w (y , s) = Lift {j = LevelOf Y} (FP (F y) w s)
    FP (⊗e Fl Fr) _ (((wl , wr), _) , sl , sr) = Lift {j = ℓX} (FP Fl wl sl ⊎ FP Fr wr sr)

    F-inX : (F : Functor X ℓ) (w : String) (s : FS F w)
      (p : FP F w s)
      → X × String
    F-inX (Var a) w s p = a , w
    F-inX (&e B F) w s (b , p) = F-inX (F b) w (s b) p -- F-inX (F b) w (s b) p
    F-inX (⊕e B F) w (b , s) (lift p) = F-inX (F b) w s p
    F-inX (⊗e Fl Fr) _ (sp , sl , sr) (lift (inl p)) =
      F-inX Fl (sp .fst .fst) sl p
    F-inX (⊗e Fl Fr) _ (sp , sl , sr) (lift (inr p)) =
      F-inX Fr (sp .fst .snd) sr p

  Container : (F : Functor X ℓ) → (X → Grammar ℓA) → Grammar (ℓ-max ℓ (ℓ-max ℓX ℓA))
  Container {ℓ = ℓ} F A w =
    Σ[ s ∈ FS F w ]
      (∀ (p : FP F w s) →
           let ix = F-inX F w s p in
           Lift {j = ℓ} (A (ix .fst) (ix .snd)))

  module _ (F : X → Functor X ℓ) where
    μIW : X × String → Type (ℓ-max ℓ ℓX)
    μIW = IW (λ ix → FS (F (ix .fst)) (ix .snd))
             (λ ix → FP (F (ix .fst)) (ix .snd))
             (λ ix → F-inX (F (ix .fst)) (ix .snd))

  module _ {A : X → Grammar ℓA} where
    getShapeF : {B : X → Grammar ℓA}(F : Functor X ℓ)
      → ∀ w
      → ⟦ F ⟧ B w → FS F w
    getShapeF F = Inductive.map F λ a w x → tt*

    opaque
      unfolding FP _⊗_ ⊗-intro
      getSubtreeF : (F : Functor X ℓ)
        → ∀ w
        → (e : ⟦ F ⟧ A w)
        → (p : FP F w (getShapeF F _ e))
        → let ix = (F-inX F w _ p) in A (ix .fst) (ix .snd)
      getSubtreeF (Var a') w e p = e .lower
      getSubtreeF (&e B F) w e (b , p) = getSubtreeF (F b) w (e b) p
      getSubtreeF (⊕e B F) w (b , e) (lift p) = getSubtreeF (F b) w e p
      getSubtreeF (⊗e Fl Fr) w (((wl , wr) , _) , el , er) (lift (inl pl)) =
        getSubtreeF Fl wl el pl
      getSubtreeF (⊗e Fl Fr) w (((wl , wr) , _) , el , er) (lift (inr pr)) =
        getSubtreeF Fr wr er pr

      nodeF : ∀ {A : X → Grammar ℓA}(F : Functor X ℓ)
        → ∀ w
        → (s : FS F w)
        → (∀ (p : FP F w s) →
             let ix = F-inX F w s p in
             A (ix .fst) (ix .snd)
          )
        → ⟦ F ⟧ A w
      nodeF (k A) w s subtree = lift (s .lower)
      nodeF (Var x') w s subtree = lift (subtree tt*)
      nodeF (&e Y F) w s subtree y =
        nodeF (F y) w (s y) (λ p → subtree (y , p))
      nodeF (⊕e Y F) w (y , s) subtree = y , nodeF (F y) w s (subtree ∘ lift)
      nodeF (⊗e Fl Fr) w (((wl , wr) , w≡wlwr) , sl , sr) subtree =
        ((wl , wr) , w≡wlwr)
          , (nodeF Fl wl sl (subtree ∘ lift ∘ inl))
          , ((nodeF Fr wr sr (subtree ∘ lift ∘ inr)))

      reconstructF : ∀ (F : Functor X ℓ)
        → ∀ w
        → (t : ⟦ F ⟧ A w)
        → nodeF F w (getShapeF F w t) (getSubtreeF F w t) ≡ t
      reconstructF (k A) w t = refl
      reconstructF (Var y) w t = refl
      reconstructF (&e Y F) w t i y = reconstructF (F y) w (t y) i
      reconstructF (⊕e Y F) w (y , t) i = y , (reconstructF (F y) w t i)
      reconstructF (⊗e Fl Fr) w (((wl , wr), sp) , tl , tr) i =
        ((wl , wr) , sp) , (reconstructF Fl wl tl i , reconstructF Fr wr tr i)

    isSet⟦F⟧ : ∀ (F : Functor X ℓ)
      → isSetValued F
      → (A : X → SetGrammar ℓA)
      → isSetGrammar (⟦ F ⟧ (λ x → ⟨ A x ⟩))
    isSet⟦F⟧ (k _) isSetF A = isSetGrammarLift (isSetGrammarLower isSetF)
    isSet⟦F⟧ (Var x) isSetF A = isSetGrammarLift (A x .snd)
    isSet⟦F⟧ (&e Y F) isSetF A =
      isSetGrammar&ᴰ (λ b → isSet⟦F⟧ (F b) (isSetF b) A)
    isSet⟦F⟧ (⊕e Y F) isSetF A =
      isSetGrammar⊕ᴰ (isSetF .fst) (λ b → isSet⟦F⟧ (F b) (isSetF .snd b) A)
    isSet⟦F⟧ (⊗e Fl Fr) isSetF A =
      isSetGrammar⊗ (isSet⟦F⟧ Fl (isSetF .fst) A) (isSet⟦F⟧ Fr (isSetF .snd) A)

    isSetμIW : ∀ (F : X → Functor X ℓ) → (∀ x → isSetValued (F x))
      → ∀ ix → isSet (μIW F ix)
    isSetμIW F isSetF  =
      isOfHLevelSuc-IW 1 (λ ix →
        (isSetGrammar≅
          (map≅ (F (ix .fst)) (λ _ → sym≅ (LiftG≅ ℓA _) ≅∙ LiftG≅ ℓX _))
          ((isSet⟦F⟧ (F (ix .fst)) (isSetF (ix .fst))
            λ _ → (λ _ → Unit*) , λ _ → isSetUnit*
          ))) (ix .snd)
      )

  {-# TERMINATING #-}
  encode : (F : X → Functor X ℓ) → ∀ ix → μ F (ix .fst) (ix .snd) → μIW F ix
  encode F (x , w) (roll .w op⟨m⟩) =
    node (Inductive.map (F x) _ w op⟨m⟩)
      λ p → encode F _ (getSubtreeF (F x) w op⟨m⟩ p)

  decode : (F : X → Functor X ℓ) → ∀ ix → μIW F ix → μ F (ix .fst) (ix .snd)
  decode F (x , w) (node s subtree) =
    roll _ (nodeF {A = μ F} (F x) w s λ p →
      decode F (F-inX (F x) w s p) (subtree p))

  opaque
    unfolding FP _⊗_ getSubtreeF nodeF
    {-# TERMINATING #-}
    isRetract : ∀ (F : X → Functor X ℓ) x w
      → (z : μ F x w) → decode F (x , w) (encode F (x , w) z) ≡ z
    isRetract F x w (roll .w t) = cong (roll w)
      (cong (nodeF {A = μ F} (F x) w (getShapeF {A = μ F} (F x) w t)) (funExt λ p → isRetract F _ _ _)
      ∙ reconstructF (F x) w t)

isSetGrammarμ : ∀ {X : Type ℓX}
  → (F : X → Functor X ℓ)
  → (∀ x → isSetValued (F x))
  → ∀ x → isSetGrammar (μ F x)
isSetGrammarμ {X = X} F isSetValuedF x w =
  isSetRetract (encode F (x , w)) (decode F (x , w)) (isRetract F x w)
    (isSetμIW {A = μ F} F isSetValuedF (x , w))
