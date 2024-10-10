open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module Term.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism

open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Helper

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

{-- Embed the linear typing rules
 -- These correspond to terms like x : g ⊢ M : g'
 -- with the caveat that derivations
 -- x : g , y : h ⊢ M : g'
 -- are represented as
 -- x : g ⊗ h ⊢ M : g'
 --
 -- Likewise, we represent the empty context with the empty grammar
 -- ∙ ⊢ M : g
 -- is given as
 -- x : ε-grammar ⊢ M : g
 --}


-- Using a weird recursion scheme to avoid extra empty appends at the end
StringTy : (gs : List (Grammar ℓg)) → Type ℓ-zero
StringTy [] = String
StringTy (g ∷ []) = String
StringTy (g ∷ g' ∷ gs) = String × StringTy (g' ∷ gs)

mkString : {gs : List (Grammar ℓg)} → StringTy gs → String
mkString {gs = []} ws = []
mkString {gs = g ∷ []} w = w
mkString {gs = (g ∷ g' ∷ gs)} (w , ws) = w ++ mkString ws

mkParseTys : {gs : List (Grammar ℓg)} → StringTy gs → Type ℓg
mkParseTys {gs = []} w = Unit*
mkParseTys {gs = (g ∷ [])} w = g w
mkParseTys {gs = (g ∷ g' ∷ gs)} (w , ws) = g w × mkParseTys ws

module _ (gs : List (Grammar ℓg)) (h : Grammar ℓg) where
  Term : Type ℓg
  Term = ∀ (ws : StringTy gs) → mkParseTys ws → h (mkString ws)

  infix 1 Term
  syntax Term gs h = gs ⊢ h

id : g ∷ [] ⊢ g
id ws pg = pg

seq :
  { Γ : List (Grammar ℓg) } →
  Γ ⊢ h →
  [ h ] ⊢ k →
  Γ ⊢ k
seq e e' ws ps = e' (mkString ws) (e ws ps)
-- _ p = e' _ (e _ p)

_∘g'_ :
  { Γ : List (Grammar ℓg) } →
  [ h ] ⊢ k →
  Γ ⊢ h →
  Γ ⊢ k
_∘g'_ e e' = seq e' e

infixr 9 _∘g'_
syntax seq e e' = e ⋆ e'

-- isMono :
--   g ⊢ h → Typeω
-- isMono {g = g}{h = h} f =
--   ∀ {ℓk}{k : Grammar ℓk} (e e' : k ⊢ g) →
--     f ∘g e ≡ f ∘g e' → e ≡ e'

-- Mono∘g : (e : g ⊢ h) (e' : h ⊢ k) →
--   isMono e' → isMono e → isMono (e' ∘g e)
-- Mono∘g e e' mon-e mon-e' f f' e'ef≡e'ef' =
--   mon-e' f f' (mon-e (e ∘g f) (e ∘g f') e'ef≡e'ef')
