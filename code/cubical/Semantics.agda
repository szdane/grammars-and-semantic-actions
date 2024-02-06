{-# OPTIONS --lossy-unification #-}
module Semantics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.List
open import Cubical.Data.FinSet
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Bool renaming (_⊕_ to _⊕B_)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
-- open import Cubical.Data.Fin.Base renaming (Fin to Finℕ)
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Category.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

open import Cubical.Tactics.Reflection

private
  variable ℓ ℓ' : Level

module Semantics ℓ (Σ₀ : hSet ℓ) where
  String : Type ℓ
  String = List (Σ₀ .fst)

  isSetString : isSet String
  isSetString = isOfHLevelList 0 (Σ₀ .snd)

  isGroupoidString : isGroupoid String
  isGroupoidString = isSet→isGroupoid isSetString

  Splitting : String → Type ℓ
  Splitting w = Σ[ (w₁ , w₂) ∈ String × String ] (w ≡ w₁ ++ w₂)

  isSetSplitting : (w : String) → isSet (Splitting w)
  isSetSplitting w = isSetΣ (isSet× isSetString isSetString) λ s → isGroupoidString w (s .fst ++ s .snd)

  Grammar : Type (ℓ-suc ℓ)
  Grammar = String → hSet ℓ

  open ListPath
  ILin : Grammar
  ILin w = (w ≡ []) , isGroupoidString w []

  _⊗_ : Grammar → Grammar → Grammar
  (g ⊗ g') w = (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × g' (s .fst .snd) .fst) ,
    isSetΣ (isSetSplitting w) λ s → isSet× (g (s .fst .fst) .snd) (g' (s .fst .snd) .snd)

  literal : (Σ₀ .fst) → Grammar
  literal c w = ([ c ] ≡ w) , isGroupoidString ([ c ]) w

  _-⊗_ : Grammar → Grammar → Grammar
  (g -⊗ g') w = {!!}
  -- ( ∀ ( w' : String ) → g w' .fst × g' (w' ++ w) .fst) ,
    -- isSetΣ isSetString λ w' → isSet× (g w' .snd) (g' (w' ++ w) .snd)

  -- TODO
  _⊗-_ : Grammar → Grammar → Grammar
  (g ⊗- g') w = (Σ[ w' ∈ String ] g (w ++ w') .fst × g' w .fst) ,
    isSetΣ isSetString λ w' → isSet× (g (w ++ w') .snd) (g' w .snd)

  -- ΠLin : Grammar
  -- ΠLin :

  -- ΣLin : Grammar
  -- ΣLin :

  ⊤Lin : Grammar
  ⊤Lin w = Unit* , isSetUnit*

  _&_ : Grammar → Grammar → Grammar
  (g & g') w = (g w .fst × g' w .fst) ,
    isSet× (g w .snd) (g' w .snd)

  _⊕_ : Grammar → Grammar → Grammar
  (g ⊕ g') w = (g w .fst ⊎ g' w .fst) ,
    isSet⊎ (g w .snd) (g' w .snd)

  --TODO bot

  {-# TERMINATING #-}
  KL*gg : Grammar → Grammar
  KL*gg g = ILin ⊕ (g ⊗ (KL*gg g))
  -- KL*gg g w = (ILin w .fst) ⊎ (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × (KL*gg g (s .fst .snd) .fst)) , {!!}

  -- TODO exponential

  ParseTransformer : Grammar → Grammar → Type ℓ
  ParseTransformer g g' = ∀ {w} → g w .fst → g' w .fst

  data KL*Ty (g : Grammar) (w : String) : Type ℓ where
    nil : ILin w .fst → (KL*Ty g w)
    cons : (Σ[ s ∈ Splitting w ] g (s .fst .fst) .fst × KL*Ty g (s .fst .snd)) → KL*Ty g w

  isSetKL*Ty : (g : Grammar) → (w : String) → isSet (KL*Ty g w)
  isSetKL*Ty g w = {!!}

  KL* : (g : Grammar) → Grammar
  KL* g w = (KL*Ty g w , isSetKL*Ty g w)


  -- TODO FinSet instead of Fin 2
  -- matrix, δ transition function presentation
  data NFA₀ (c : Σ₀ .fst) : (state : Fin 2) → (w : String) → Type (ℓ-suc ℓ)
  data NFA₀ c where
    nil : NFA₀ c (fsuc fzero) []
    cons : ∀ {w'} → (literal c) (c ∷ w') .fst → NFA₀ c (fsuc fzero) w' → NFA₀ c fzero (c ∷ w')


  data NFAαStart (c : Σ₀ .fst) (w : String) : Type (ℓ-suc ℓ)
  data NFAαEnd (c : Σ₀ .fst) (w : String) : Type (ℓ-suc ℓ)

  data NFAαStart c w where
    st : (literal c) w .fst → NFAαEnd c ([]) → NFAαStart c w
  data NFAαEnd c w where
    end : NFAαEnd c w


module _ where
  data αβ : Set ℓ-zero where
    α : αβ
    β : αβ

  isSetαβ : isSet αβ
  isSetαβ = {!!}

  open Semantics ℓ-zero (αβ , isSetαβ)
  w : String
  w = α ∷ β ∷ α ∷ β ∷ α ∷ []

  g : Grammar
  g = (KL* (literal α ⊗ literal β) ⊗ literal α)

  p : g w .fst
  p = ((α ∷ β ∷ α ∷ β ∷ [] , α ∷ []) , refl) ,
      cons (((α ∷ β ∷ [] , α ∷ β ∷ []) , refl) ,
           ((([ α ] , [ β ]) , refl) , (refl , refl)) ,
           (cons ((((α ∷ β ∷ []) , []) , refl) ,
             (((([ α ] , [ β ]) , refl) , (refl , refl)) , (nil refl))))) ,
      refl

  p' : ((KL*gg (literal α ⊗ literal β)) ⊗ literal α) w .fst
  p' =
    (((α ∷ β ∷ α ∷ β ∷ []) , (α ∷ [])) , refl) ,
    inr (
      ((((α ∷ β ∷ [])) , ((α ∷ β ∷ []))) , refl) ,
      (((([ α ] , [ β ]) , refl) , (refl , refl)) ,
        (inr
          ((((α ∷ β ∷ []) , []) , refl) ,
            (((([ α ] , [ β ]) , refl) , (refl , refl)) ,
          inl refl))
        )
      )
    ) ,
    refl

  w' = α ∷ []

  -- pnfa : NFA₀ α w' (fsuc fzero)
  -- pnfa = start refl (end refl)

  pα : (literal α) w' .fst
  pα = refl

  open Iso

  nfaα-iso-to-α : (word : String) → Iso (NFAαStart α word) (literal α word .fst)
  fun (nfaα-iso-to-α word) (st lit end) = lit
  inv (nfaα-iso-to-α word) lit = st lit (end)
  rightInv (nfaα-iso-to-α word) _ = refl
  leftInv (nfaα-iso-to-α word) (st lit end) = cong (λ x → st lit x) refl

  -- NFA₀-iso : (word : String) → Iso (NFA₀ α word (fzero)) (literal α word .fst)
  -- fun (NFA₀-iso word) (start a b c) = b
  -- fun (NFA₀-iso word) (end b) = {!!}
  -- inv (NFA₀-iso word) = {!!}
  -- rightInv (NFA₀-iso word) = {!!}
  -- leftInv (NFA₀-iso word) = {!!}
