open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Term.Base Alphabet
open import Cubical.Data.Equality as Eq
-- open import Term.Bilinear Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

_⊗'_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
(g ⊗' g') w = Σ[ s ∈ Splitting w ] g (s .fst .fst) × g' (s .fst .snd)
infixr 5 _⊗'_
opaque
  _⊗_ : Grammar ℓg → Grammar ℓh → Grammar (ℓ-max ℓg ℓh)
  _⊗_ = _⊗'_

infixr 5 _⊗_

opaque
  unfolding _⊗_
  -- ⊗-elim : g ,, h ⊢ k → [ g ⊗ h ] ⊢ k
  -- ⊗-elim {k = k} f w (((w1 , w2) , w≡w1++w2) , gp , hp) =
  --   subst k (sym w≡w1++w2) (f w1 w2 gp hp)

  -- ⊗-intro' : g ,, h ⊢ (g ⊗ h)
  -- ⊗-intro' w1 w2 gp hp = splitting++ w1 w2 , gp , hp

  -- ⊗-β : ∀ (f : g ,, h ⊢ k)
  --   → (⊗-elim {k = k} f ∘b ⊗-intro') ≡ f
  -- ⊗-β {k = k} f i w1 w2 gp hp = substRefl {B = k} (f w1 w2 gp hp) i

--   -- ⊗-η : ∀ (f : g ⊗ h ⊢ k)
--   --   → f ≡ ⊗-elim {k = k} (f ∘b ⊗-intro')
--   -- ⊗-η f i w x = {!!}

--   -- because ⊗ is opaque,
--   -- same-splits and same-parses are needed so that the interface of
--   -- ⊗ doesn't leak in the type signature of ⊗PathP
--   same-splits :
--     {g : I → Grammar ℓg}{h : I → Grammar ℓh}
--     {w : I → String}
--     → (p : (g i0 ⊗ h i0) (w i0))
--     → (q : (g i1 ⊗ h i1) (w i1))
--     → Type ℓ-zero
--   same-splits p q = p .fst .fst ≡ q .fst .fst

--   same-parses :
--     {g : I → Grammar ℓg}{h : I → Grammar ℓh}
--     {w : I → String}
--     → (p : (g i0 ⊗ h i0) (w i0))
--     → (q : (g i1 ⊗ h i1) (w i1))
--     → (s≡ : same-splits {g = g}{h = h}{w = w} p q)
--     → Type (ℓ-max ℓg ℓh)
--   same-parses {g = g} {h = h} p q s≡ =
--     PathP (λ i → g i (s≡ i .fst) × h i (s≡ i .snd)) (p .snd) (q .snd)

--   ⊗PathP :
--     {g : I → Grammar ℓg}{h : I → Grammar ℓh}
--     {w : I → String}
--     → {p : (g i0 ⊗ h i0) (w i0)}
--     → {q : (g i1 ⊗ h i1) (w i1)}
--     → (s≡ : same-splits {g = g} {h = h} {w = w} p q)
--     → same-parses p q s≡
--     → PathP (λ i → (g i ⊗ h i) (w i)) p q
--   ⊗PathP s≡ p≡ = ΣPathP (SplittingPathP s≡ , p≡)

--   ⊗≡ : ∀ {g : Grammar ℓg}{h : Grammar ℓh}{w}
--     → (p p' : (g ⊗ h) w)
--     → (s≡ : same-splits {g = λ _ → g}{h = λ _ → h}{w = λ _ → w} p p')
--     → same-parses p p' s≡
--     → p ≡ p'
--   ⊗≡ p p' s≡ p≡ = ⊗PathP s≡ p≡

  ⊗-intro :
    g ∷ g' ∷ [] ⊢ g ⊗ g'
  ⊗-intro ws (pg , pg') = ((_ , Eq.refl)) , (pg , pg')

_,⊗_ = ⊗-intro
infixr 20 _,⊗_
