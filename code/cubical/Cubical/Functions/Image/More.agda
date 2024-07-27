module Cubical.Functions.Image.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Image

private
  variable
    ℓ : Level
    A B : Type ℓ

isSetImage : isSet B → {f : A → B} → isSet (Image f)
isSetImage isSetB = isSetΣ isSetB (isProp→isSet ∘ isPropIsInImage _)

