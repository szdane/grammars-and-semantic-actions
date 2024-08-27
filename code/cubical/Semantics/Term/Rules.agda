open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

module Semantics.Term.Rules ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma

open import Semantics.Grammar (Σ₀ , isSetΣ₀)
open import Semantics.Term.Base (Σ₀ , isSetΣ₀)
open import Semantics.Helper

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g : Grammar ℓg
    h : Grammar ℓh
    k : Grammar ℓk
    l : Grammar ℓl

id : g ⊢ g
id _ x = x

seq :
  g ⊢ h →
  h ⊢ k →
  g ⊢ k
seq e e' _ p = e' _ (e _ p)
-- e' (e p)

_∘g_ :
  h ⊢ k →
  g ⊢ h →
  g ⊢ k
_∘g_ e e' = seq e' e

infixr 9 _∘g_
syntax seq e e' = e ⋆ e'

⊗-intro :
  g ⊢ h →
  k ⊢ l →
  g ⊗ k ⊢ h ⊗ l
⊗-intro e e' _ p =
  p .fst , (e _ (p .snd .fst)) , (e' _ (p .snd .snd))

⊗-unit-r :
  g ⊗ ε-grammar ⊢ g
⊗-unit-r {g = g} _ (((w' , []') , w≡w'++[]') , p⟨w'⟩ , []'≡[]) =
  subst g (sym (++-unit-r _)
          ∙ cong (w' ++_) (sym []'≡[])
          ∙ sym w≡w'++[]')
    p⟨w'⟩

⊗-unit-r⁻ :
  g ⊢ g ⊗ ε-grammar
⊗-unit-r⁻ _ p =
  ((_ , []) , (sym (++-unit-r _))) , (p , refl)

isPropε : ∀ w → isProp (ε-grammar w)
isPropε w = isSetString _ _

rectify :
  ∀ {w w'}{g : Grammar ℓg}
  → {p : g w}{q : g w'}
  → {w≡ w≡' : w ≡ w'}
  → PathP (λ i → g (w≡  i)) p q
  → PathP (λ i → g (w≡' i)) p q
rectify {w = w}{w'}{g = g}{p = p}{q = q} = subst {A = w ≡ w'} (λ w≡ → PathP (λ i → g (w≡ i)) p q)
  (isSetString _ _ _ _)

⊗-unit-rr⁻ :
  ∀ {g : Grammar ℓg}
  → ⊗-unit-r⁻ {g = g} ∘g ⊗-unit-r ≡ id
⊗-unit-rr⁻ {g = g} = funExt λ w → funExt λ (((w' , []') , w≡w'++[]') , p⟨w'⟩ , []'≡[]) →
  let w≡w' = (sym (sym (++-unit-r _)
          ∙ cong (w' ++_) (sym []'≡[])
          ∙ sym w≡w'++[]'))
  in
  ⊗≡ _ _
    (≡-× w≡w'
      (sym []'≡[]))
    (ΣPathP
      ( symP (subst-filler g (sym w≡w') p⟨w'⟩)
      , isProp→PathP (λ _ → isPropε _) refl []'≡[]))

⊗-unit-r⁻r : ∀ {g : Grammar ℓg}
  → ⊗-unit-r {g = g} ∘g ⊗-unit-r⁻ ≡ id
⊗-unit-r⁻r {g = g} = funExt λ w → funExt λ p →
  let
    w≡w : w ≡ w
    w≡w =       (λ i →
         (hcomp
          (doubleComp-faces (λ _ → w)
           (λ i₁ →
              hcomp (doubleComp-faces (λ _ → w ++ []) (λ i₂ → ++-unit-r w i₂) i₁)
              (w ++ []))
           i)
          (++-unit-r w (~ i))))
  in
  subst (λ w≡w → subst g w≡w p ≡ p) (isSetString _ _ refl w≡w)
    (substRefl {B = g} p)

⊗-unit-l :
  ε-grammar ⊗ g ⊢ g
⊗-unit-l {g = g} _ p =
  transport
    (cong g (cong (_++  p .fst .fst .snd)
      (sym (p .snd .fst)) ∙ sym (p .fst .snd)))
    (p .snd .snd)

⊗-unit-l⁻ :
  g ⊢ ε-grammar ⊗ g
⊗-unit-l⁻ _ p =
  (([] , _) , refl) , (refl , p)

⊗-assoc :
  g ⊗ (h ⊗ k) ⊢ (g ⊗ h) ⊗ k
⊗-assoc _ p =
  ((fst p .fst .fst ++ fst (p .snd .snd) .fst .fst , fst (p .snd .snd) .fst .snd) ,
    p .fst .snd ∙
    cong (p .fst .fst .fst ++_) (p .snd .snd .fst .snd) ∙
    sym
    (++-assoc
      (p .fst .fst .fst)
      (p .snd .snd .fst .fst .fst)
      (p .snd .snd .fst .fst .snd))) ,
  ((((fst p .fst .fst , fst (p .snd .snd) .fst .fst) ,
    refl) ,
  ((p .snd .fst) , (p .snd .snd .snd .fst))) , (p .snd .snd .snd .snd))

⊗-assoc⁻ :
  (g ⊗ h) ⊗ k ⊢ g ⊗ (h ⊗ k)
⊗-assoc⁻ _ p =
  (((fst (p .snd .fst) .fst .fst) , (fst (p .snd .fst) .fst .snd ++ fst p .fst .snd)) ,
    (p .fst .snd ∙
    cong (_++ p .fst .fst .snd) (p .snd .fst .fst .snd) ∙
    ++-assoc
      (p .snd .fst .fst .fst .fst)
      (p .snd .fst .fst .fst .snd)
      (p .fst .fst .snd))) ,
    (p .snd .fst .snd .fst ,
    (((fst (p .snd .fst) .fst .snd , fst p .fst .snd) ,
      refl) ,
    (p .snd .fst .snd .snd ,
    p .snd .snd)))

⊗-assoc∘⊗-assoc⁻≡id :
 ⊗-assoc {g = g}{h = h}{k = k} ∘g ⊗-assoc⁻ ≡ id
⊗-assoc∘⊗-assoc⁻≡id = funExt λ w → funExt λ p →
  ⊗≡ _ _
    (≡-× (λ i → p .snd .fst .fst .snd (~ i)) refl)
    (ΣPathP (
      (⊗PathP
        (≡-× refl refl)
        (≡-× refl refl)) ,
      refl))

⊗-assoc⁻∘⊗-assoc≡id :
 ⊗-assoc⁻ {g = g}{h = h}{k = k} ∘g ⊗-assoc ≡ id
⊗-assoc⁻∘⊗-assoc≡id = funExt λ w → funExt λ p →
  ⊗≡ _ _
    (≡-× refl (sym (p .snd .snd .fst .snd)))
    (ΣPathP (
      refl ,
      (⊗PathP (≡-× refl refl)
        (ΣPathP (refl , refl)))))

-⊗-intro :
  g ⊗ h ⊢ k →
  h ⊢ g -⊗ k
-⊗-intro e _ p w' q =
  e _ ((_ , refl) , (q , p))

-⊗-app :
  g ⊗ (g -⊗ h) ⊢ h
-⊗-app {h = h} _ p = subst h (sym (p .fst .snd)) (p .snd .snd _ (p .snd .fst))

-⊗-intro⁻ :
  g ⊢ h -⊗ k →
  h ⊗ g ⊢ k
-⊗-intro⁻ {h = h}{k = k} f =
  (⊗-intro (id {g = h}) f) ⋆ -⊗-app

-⊗-intro∘-⊗-intro⁻≡id :
  (e : g ⊢ h -⊗ k) →
  -⊗-intro {g = h}{h = g}{k = k}(-⊗-intro⁻ e) ≡ e
-⊗-intro∘-⊗-intro⁻≡id e = funExt λ w → funExt λ pg →
  funExt λ w' → funExt λ ph → transportRefl _

-⊗-intro⁻∘-⊗-intro≡id :
  (e : g ⊗ h ⊢ k) →
  -⊗-intro⁻ {g = h}{h = g}{k = k}(-⊗-intro e) ≡ e
-⊗-intro⁻∘-⊗-intro≡id {k = k} e = funExt λ w → funExt λ p⊗ →
  fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
    (⊗PathP (≡-× refl refl) (≡-× refl refl)))

-- TODO : this needs a better name
-⊗-curry :
  (g -⊗ h) ⊗ k ⊢ g -⊗ (h ⊗ k)
-⊗-curry {g = g}{h = h}{k = k} =
  -⊗-intro {g = g}{h = (g -⊗ h) ⊗ k}{k = h ⊗ k}
    (⊗-assoc ⋆ ⊗-intro -⊗-app id)

-⊗-β :
  (m : (g ⊗ h) ⊢ k) →
  (-⊗-intro⁻ {g = h}{h = g}{k = k} (-⊗-intro {g = g}{h = h}{k = k} m))
    ≡
  m
-⊗-β {k = k} m = funExt (λ w → funExt (λ p⊗ →
  fromPathP {A = λ i → k (p⊗ .fst .snd (~ i))}
    (congP (λ _ → m _) (⊗PathP refl refl))))

-⊗-η :
  (f : g ⊢ h -⊗ k) →
  f
    ≡
  (-⊗-intro {g = h}{h = g}{k = k} (-⊗-intro⁻ {g = g}{h = h}{k = k} f))
-⊗-η f = funExt (λ w → funExt (λ p⊗ → funExt (λ w' → funExt
  (λ q⊗ → sym (transportRefl (f _ p⊗ w' q⊗))))))


⟜-intro :
  g ⊗ h ⊢  k →
  g ⊢ k ⊗- h
⟜-intro e _ p w' q =
  e _ ((_ , refl) , p , q)

⟜-app :
  (g ⊗- h) ⊗ h ⊢ g
⟜-app {g = g} _ (((w' , w'') , w≡w'++w'') , f , inp) =
  subst g (sym w≡w'++w'') (f _ inp)

⟜-intro⁻ :
  g ⊢ h ⊗- k →
  g ⊗ k ⊢ h
⟜-intro⁻ {h = h}{k = k} f =
  ⟜-app ∘g ⊗-intro f (id {g = k})

⟜-η :
  (e : g ⊢ h ⊗- k) →
  ⟜-intro {g = g}{h = k}{k = h}(⟜-intro⁻ e) ≡ e
⟜-η e = funExt λ w → funExt λ pg →
  funExt λ w' → funExt λ pk → transportRefl _

⟜-β :
  (e : g ⊗ h ⊢ k) →
  ⟜-intro⁻ {g = g}{h = k}{k = h}(⟜-intro e) ≡ e
⟜-β e = funExt λ w → funExt λ p⊗ →
  fromPathP (congP₂ (λ _ → e) (sym (p⊗ .fst .snd))
    (⊗PathP refl refl))

⟜-curry :
  g ⊗ (h ⊗- k) ⊢ (g ⊗ h) ⊗- k
⟜-curry {g = g}{h = h}{k = k} =
  ⟜-intro (⊗-intro id ⟜-app ∘g ⊗-assoc⁻)

⊤-intro :
  g ⊢ ⊤-grammar {ℓG = ℓ}
⊤-intro _ _ = tt*

⊥-elim :
  ⊥-grammar ⊢ g
⊥-elim _ = ⊥.elim

⊥-η : ∀ (f f' : ⊥-grammar ⊢ g)
  → f ≡ f'
⊥-η _ _ = funExt λ _ → funExt ⊥.elim

&-intro :
  g ⊢ h →
  g ⊢ k →
  g ⊢ h & k
&-intro e e' _ p =
  e _ p , e' _ p

&-π₁ :
  g & h ⊢ g
&-π₁ _ p = p .fst

&-π₂ :
  g & h ⊢ h
&-π₂ _ p = p .snd

&-β₁ :
  (e₁ : g ⊢ h) →
  (e₂ : g ⊢ k) →
  (&-intro e₁ e₂) ⋆ &-π₁ 
    ≡
  e₁
&-β₁ e₁ e₂ = refl

&-β₂ :
  (e₁ : g ⊢ h) →
  (e₂ : g ⊢ k) →
  (&-intro e₁ e₂) ⋆ &-π₂
    ≡
  e₂
&-β₂ e₁ e₂ = refl

&-η :
  (e : g ⊢ h & k) →
  (&-intro {g = g}{h = h}{k = k}
    (e ⋆ &-π₁)
    (e ⋆ &-π₂))
  ≡
  e
&-η e = refl

⊕-inl :
  g ⊢ g ⊕ h
⊕-inl _ p = inl p

⊕-inr :
  g ⊢ h ⊕ g
⊕-inr _ p = inr p

⊕-elim :
  g ⊢ h →
  k ⊢ h →
  g ⊕ k ⊢ h
⊕-elim eg eh _ p =
  Sum.elim
    (λ pg → eg _ pg)
    (λ ph → eh _ ph)
    p

⊕≡ :
  (f f' : g ⊕ k ⊢ h)
  → (f ∘g ⊕-inl ≡ f' ∘g ⊕-inl)
  → (f ∘g ⊕-inr ≡ f' ∘g ⊕-inr)
  → f ≡ f'
⊕≡ f f' f≡f'inl f≡f'inr = funExt λ w → funExt λ
  { (inl x) → funExt⁻ (funExt⁻ f≡f'inl _) x
  ; (inr x) → funExt⁻ (funExt⁻ f≡f'inr _) x }

⊕-βl :
  (e₁ : g ⊢ g ⊕ h) →
  (e₂ : h ⊢ g ⊕ h) →
  ⊕-inl ⋆ ⊕-elim e₁ e₂
    ≡
  e₁
⊕-βl e₁ e₂ = refl

⊕-βr :
  (e₁ : g ⊢ g ⊕ h) →
  (e₂ : h ⊢ g ⊕ h) →
  ⊕-inr ⋆ ⊕-elim e₁ e₂
    ≡
  e₂
⊕-βr e₁ e₂ = refl

⊕-η :
  (e : g ⊕ h ⊢ k) →
  (⊕-elim {g = g}{h = k}{k = h}
    (⊕-inl ⋆ e)
    (⊕-inr ⋆ e)
  )
    ≡
    e
⊕-η e i _ (inl x) = e _ (inl x)
⊕-η e i _ (inr x) = e _ (inr x)

⇒-intro :
  g & h ⊢ k →
  g ⊢ h ⇒ k
⇒-intro e _ pg = λ ph → e _ (pg , ph)

⇒-app :
  g & (g ⇒ h) ⊢ h
⇒-app _ (pg , f) = f pg

KL*-elim :
  ε-grammar ⊢ g →
  h ⊗ g ⊢ g →
  KL* h ⊢ g
KL*-elim pε p⊗ _ (nil _ x) = pε _ x
KL*-elim {g}{h} pε p⊗ _ (cons _ x) =
  p⊗ _ ((x .fst) , ((x .snd .fst) , (KL*-elim pε p⊗ _ (x .snd .snd))))

foldKL*r = KL*-elim

foldKL*l :
  ε-grammar ⊢ g →
  g ⊗ h ⊢ g →
  KL* h ⊢ g
foldKL*l {g = g}{h = h} pε p⊗ =
  seq {g = KL* h}{h = g -⊗ g}{k = g}
    (foldKL*r {g = g -⊗ g}{h = h}
      (-⊗-intro {g = g}{h = ε-grammar}{k = g} ⊗-unit-r)
      (-⊗-intro {g = g}{h = h ⊗ (g -⊗ g)}{k = g}
        (seq {h = (g ⊗ h) ⊗ (g -⊗ g)}
          (⊗-assoc {g = g}{h = h}{k = g -⊗ g})
          (seq {h = g ⊗ (g -⊗ g)}
            (⊗-intro {g = g ⊗ h}{h = g}{k = g -⊗ g}{l = g -⊗ g} p⊗ (id {g = g -⊗ g}))
            -⊗-app))))
    (seq {g = g -⊗ g}{h = g ⊗ (g -⊗ g)}{k = g}
      (seq {h = ε-grammar ⊗ (g -⊗ g)}
        (⊗-unit-l⁻ {g = g -⊗ g})
        (⊗-intro {g = ε-grammar}{h = g}{k = g -⊗ g}{l = g -⊗ g} pε (id {g = g -⊗ g})))
      -⊗-app)
