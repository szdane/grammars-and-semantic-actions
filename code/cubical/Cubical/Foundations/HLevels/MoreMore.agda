module Cubical.Foundations.HLevels.MoreMore where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

private
  variable ℓ ℓ' : Level

isPropLift :
  {L L' : Level} →
  {A : Type L} →
  isProp A → isProp (Lift {L}{L'} A)
isPropLift = isOfHLevelLift 1

isSetLift :
  {L L' : Level} →
  {A : Type L} →
  isSet A → isSet (Lift {L}{L'} A)
isSetLift = isOfHLevelLift 2

isGroupoidLift :
  {L L' : Level} →
  {A : Type L} →
  isGroupoid A → isGroupoid (Lift {L}{L'} A)
isGroupoidLift = isOfHLevelLift 3

isPropCod→isProp≃ :
  {a : Type ℓ}{b : Type ℓ'} →
  isProp b → isProp (a ≃ b)
isPropCod→isProp≃ isPropB =
  isPropΣ
     (isProp→ isPropB)
    λ f → isPropIsEquiv f
