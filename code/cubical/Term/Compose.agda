open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Term.Compose (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Term.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

_∘b_ :
  { k : Grammar ℓg} →
  { Γ : List (Grammar ℓg) } →
  g ∷ h ∷ [] ⊢ k →
  Γ ⊢ g ⊗ h →
  Γ ⊢ k
_∘b_ {k = k} {Γ = Γ} e e' ws ps = {!!}
  -- where
  -- opaque
  --   unfolding _⊗_
  --   help' : (g ⊗ h) (mkString ws) → k (mkString ws)
  --   help' (((w , w') , Eq.refl) , pg , ph) = {!!}

  --   help : k {!!}
  --   help =
  --     let gh⊗ = e' ws ps in
  --     {!!}
  --     -- (λ { (((w , w') , Eq.refl) , pg , ph) → {!!} }) gh⊗
  --     -- -- e (gh⊗ .fst .fst .fst , gh⊗ .fst .fst .snd) {!!}
-- seq e' e
