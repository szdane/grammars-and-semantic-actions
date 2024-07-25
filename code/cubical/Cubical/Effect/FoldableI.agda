module Cubical.Effect.FoldableI where

open import Cubical.Foundations.Prelude

private
  variable
    ℓ ℓ' ℓidx ℓacc : Level
    T : Type _

record RawFoldableIdx (Idx : Type ℓidx) (F : Type ℓ → Idx → Type ℓ') : Type ? where
  field
    suci : Idx → Idx
    ifoldr : {Acc : Idx → Type ℓacc} → (∀ i → T → Acc i → )

