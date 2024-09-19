open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.MonoidalClosed (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Helper
open import Grammar.Base Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Term.Base Alphabet
open import Term.Nullary Alphabet
open import Term.Bilinear Alphabet

private
  variable
    ℓG ℓH ℓK : Level
    g h k l : Grammar ℓG
opaque
  unfolding ε
  ε-intro : ε⊢ ε
  ε-intro = refl

  ε-elim : ∀ {g : Grammar ℓG}
    → ε⊢ g
    → ε ⊢ g
  ε-elim {g = g} g[] w w≡[] = subst g (sym w≡[]) g[]

  ε-β : ∀ (gp : ε⊢ g)
    → ε-elim {g = g} gp ∘ε ε-intro ≡ gp
  ε-β {g = g} gp = transportRefl gp

  ε-η : ∀ {g : Grammar ℓG}
   → (f : ε ⊢ g)
   → f ≡ ε-elim (f _ ε-intro)
  ε-η {g = g} f = funExt λ w → funExt λ w≡[] →
    J (λ w []≡w → f w (sym []≡w) ≡ subst g []≡w (f [] ε-intro))
      (sym (substRefl {B = g} (f [] ε-intro)))
      (sym w≡[])

opaque
  unfolding _⟜_
  ⟜-intro' :
    g ,, h ⊢ k
    → g ⊢ k ⟜ h
  ⟜-intro' f w x w' x₁ = f w w' x x₁
  ⟜-app' :
    (g ⟜ h) ,, h ⊢ g
  ⟜-app' w w' fp hp = fp w' hp

  ⟜-β' :
    ∀ (f : g ,, h ⊢ k) →
    _b∘l_ {g = k ⟜ h}{k = k} ⟜-app' (⟜-intro' f) ≡ f
  ⟜-β' f = refl

  ⟜-η' :
    ∀ (f : g ⊢ k ⟜ h) →
    f ≡ ⟜-intro' (_b∘l_ {g = k ⟜ h}{k = k} ⟜-app' f)
  ⟜-η' f = refl

  ⟜-intro'ε :
    h ⊢ k
    → ε⊢ (k ⟜ h)
  ⟜-intro'ε f = f

⟜-intro'⁻ :
  g ⊢ k ⟜ h
  → g ,, h ⊢ k
⟜-intro'⁻ {g = g}{k = k}{h = h} f = _b∘l_ {k = k} ⟜-app' f

ε-elim-l : g ⊢ h → ε ,, g ⊢ h
ε-elim-l {h = h} f = ⟜-intro'⁻ {k = h} (ε-elim (⟜-intro'ε f))

  -- ε-elim-r : g ⊢ h → g ,, ε ⊢ h
  -- ε-elim-r {h = h} f w1 w2 gp (w2≡[]) =
  --   subst h
  --     (sym (++-unit-r _) ∙ cong (w1 ++_) (sym w2≡[]))
  --     (f w1 gp)

ε-ind :
  ∀ (f f' : ε ⊢ g)
  → (f ∘ε ε-intro ≡ f' ∘ε ε-intro)
  → f ≡ f'
ε-ind f f' fε≡f'ε = ε-η f ∙ cong ε-elim fε≡f'ε ∙ sym (ε-η f')

opaque
  ⊗-elim : g ,, h ⊢ k → g ⊗ h ⊢ k
  ⊗-elim {k = k} f w (((w1 , w2) , w≡w1++w2) , gp , hp) =
    subst k (sym w≡w1++w2) (f w1 w2 gp hp)

  ⊗-intro' : g ,, h ⊢ (g ⊗ h)
  ⊗-intro' w1 w2 gp hp = splitting++ w1 w2 , gp , hp

  ⊗-β : ∀ (f : g ,, h ⊢ k)
    → (⊗-elim {k = k} f ∘b ⊗-intro') ≡ f
  ⊗-β {k = k} f i w1 w2 gp hp = substRefl {B = k} (f w1 w2 gp hp) i

  -- ⊗-η : ∀ (f : g ⊗ h ⊢ k)
  --   → f ≡ ⊗-elim {k = k} (f ∘b ⊗-intro')
  -- ⊗-η f i w x = {!!}

-- ⊗-unit-l' :
--   ε ⊗ g ⊢ g
-- ⊗-unit-l' = ⊗-elim (ε-elim-l id)

⊗-unit-l'⁻ :
  g ⊢ ε ⊗ g
⊗-unit-l'⁻ = ⊗-intro' b∘εl ε-intro

-- ⊗-unit-l'l'⁻ :
--   ⊗-unit-l'⁻ {g = g} ∘g ⊗-unit-l' ≡ id
-- ⊗-unit-l'l'⁻ = {!!}

-- ⊗-unit-r' :
--   g ⊗ ε ⊢ g
-- ⊗-unit-r' = ⊗-elim (ε-elim-r id)

⊗-unit-r'⁻ : g ⊢ g ⊗ ε
⊗-unit-r'⁻ = ⊗-intro' b∘εr ε-intro

