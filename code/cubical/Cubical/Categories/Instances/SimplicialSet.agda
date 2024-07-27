module Cubical.Categories.Instances.SimplicialSet where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Simplex
open import Cubical.Categories.Presheaf

SimplicialSetCat : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
SimplicialSetCat ℓ = PresheafCategory ΔCat ℓ

