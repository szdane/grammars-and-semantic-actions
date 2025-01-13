open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

module Grammar.KleeneStar.Inductive (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.FinSet

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Product Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Dependent Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Epsilon Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Grammar.Equalizer Alphabet
open import Grammar.Lift Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.Properties Alphabet
open import Term.Base Alphabet

private
  variable
    ℓG ℓH : Level
    g h : Grammar ℓG

module _ (g : Grammar ℓG) where
  data *Tag : Type ℓG where
    nil cons : *Tag

  *Ty : Unit* {ℓG} → Functor Unit*
  *Ty _ = ⊕e *Tag (λ { nil → k ε* ; cons → ⊗e (k g) (Var _)})

  isFinSet*Tag : isFinSet *Tag
  isFinSet*Tag =
    EquivPresIsFinSet
      (isoToEquiv (iso
        (λ { (inl tt) → nil ; (inr (inl tt)) → cons})
        (λ { nil → inl tt ; cons → inr (inl tt)})
        (λ { nil → refl ; cons → refl})
        λ { (inl tt) → refl ; (inr (inl tt)) → refl}
        ))
      (isFinSetFin {n = 2})

  KL* : Grammar ℓG
  KL* = μ *Ty _

  fold*r : Algebra *Ty (λ _ → h) → KL* ⊢ h
  fold*r alg = rec *Ty alg _

  repeatTy : Lift {j = ℓG} ℕ → Functor (Lift ℕ)
  repeatTy (lift zero) = k ε*
  repeatTy (lift (suc n)) = ⊗e (k g) (Var (lift n))

  repeat' : Lift ℕ → Grammar ℓG
  repeat' n = μ repeatTy n

  open StrongEquivalence

  repeat = ⊕[ n ∈ (Lift ℕ) ] repeat' n

  gradeAlg : Algebra *Ty λ _ → repeat
  gradeAlg _ = ⊕ᴰ-elim (λ {
      nil → ⊕ᴰ-in (lift 0) ∘g roll
    ; cons →
        ⊕ᴰ-elim (λ (lift n) → ⊕ᴰ-in (lift (suc n)) ∘g roll ∘g liftG ,⊗ liftG) ∘g
        ⊕ᴰ-distR .fun ∘g lowerG ,⊗ lowerG
    })

  grade : KL* ⊢ repeat
  grade = rec *Ty gradeAlg _

  ungradeAlg : Algebra repeatTy λ n → KL*
  ungradeAlg (lift zero) = roll ∘g ⊕ᴰ-in nil
  ungradeAlg (lift (suc a)) = roll ∘g ⊕ᴰ-in cons

  ungrade' : ∀ n → repeat' n ⊢ KL*
  ungrade' n = rec repeatTy ungradeAlg n

  ungrade : repeat ⊢ KL*
  ungrade = ⊕ᴰ-elim λ n → ungrade' n

  opaque
    unfolding ⊕ᴰ-distR ⊗-intro eq-π
    secAlg : Algebra repeatTy (λ n → equalizer (grade ∘g ungrade' n) (⊕ᴰ-in n))
    secAlg (lift zero) = eq-intro _ _ roll refl
    secAlg (lift (suc n)) =
      eq-intro _ _
        (roll ∘g id ,⊗ (liftG ∘g eq-π _ _ ∘g lowerG))
        (λ i → ⊕ᴰ-elim (λ (lift m) → ⊕ᴰ-in (lift (suc m)) ∘g roll ∘g liftG ,⊗ liftG) ∘g ⊕ᴰ-distR .fun ∘g
               id ,⊗ eq-π-pf _ _ i ∘g lowerG ,⊗ lowerG )

  opaque
    unfolding secAlg ⊕ᴰ-distR eq-π ⊗-intro eq-intro
    *continuous : StrongEquivalence KL* repeat
    *continuous .fun = grade
    *continuous .inv = ungrade
    *continuous .sec =
      ⊕ᴰ≡ _ _ (λ n →
        equalizer-section (grade ∘g ungrade' n) (⊕ᴰ-in n)
          (rec repeatTy secAlg n)
          (ind-id' repeatTy
            (compHomo repeatTy
              (initialAlgebra repeatTy)
              secAlg
              (initialAlgebra repeatTy)
              ((λ m → eq-π _ _) ,
              λ { (lift zero) → refl ; (lift (suc m)) → refl })
              (recHomo repeatTy secAlg))
            n))
    *continuous .ret =
      ind-id' *Ty
        (compHomo *Ty (initialAlgebra *Ty) gradeAlg (initialAlgebra *Ty)
          ((λ _ → ungrade) ,
          (λ _ → ⊕ᴰ≡ _ _
            λ { nil → refl
              ; cons → refl }))
          (recHomo *Ty gradeAlg)) _

  unrolled* = ⟦ *Ty _ ⟧ (μ *Ty)

  *≅unrolled* : KL* ≅ unrolled*
  *≅unrolled* = unroll≅ *Ty _

  data *TagL : Type ℓG where
    nil snoc : *TagL

  *LTy : Unit* {ℓG} → Functor Unit*
  *LTy _ = ⊕e *TagL (λ { nil → k ε* ; snoc → ⊗e (Var _) (k g)})

  *LAlg→*Alg : Algebra *LTy (λ _ → h)  → Algebra *Ty (λ _ → h ⊸ h)
  *LAlg→*Alg l-alg _ = ⊕ᴰ-elim (λ {
      nil → ⊸-intro-ε id ∘g lowerG ∘g lowerG
    ; cons → ⊸-intro (⊸-app ∘g (l-alg _ ∘g ⊕ᴰ-in snoc ∘g liftG ,⊗ liftG) ,⊗ id ∘g ⊗-assoc) ∘g lowerG ,⊗ lowerG })

  fold*l : Algebra *LTy (λ _ → h) → KL* ⊢ h
  fold*l alg = ⊸-app ∘g (alg _ ∘g ⊕ᴰ-in nil ∘g liftG ∘g liftG) ,⊗ fold*r (*LAlg→*Alg alg) ∘g ⊗-unit-l⁻

_* : Grammar ℓG → Grammar ℓG
g * = KL* g

_+ : Grammar ℓG → Grammar ℓG
g + = g ⊗ g *

_⊗[_] : Grammar ℓG → ℕ → Grammar ℓG
g ⊗[ n ] = repeat' g (lift n)

NIL : ∀ {g : Grammar ℓG} → ε ⊢ g *
NIL = roll ∘g ⊕ᴰ-in nil ∘g liftG ∘g liftG

CONS : ∀ {g : Grammar ℓG} → g ⊗ g * ⊢ g *
CONS = roll ∘g ⊕ᴰ-in cons ∘g liftG ,⊗ liftG

+→* : (g : Grammar ℓG) → g + ⊢ g *
+→* g = CONS

+-singleton : (g : Grammar ℓG) → g ⊢ g +
+-singleton g = id ,⊗ NIL ∘g ⊗-unit-r⁻

+-cons : (g : Grammar ℓG) → g ⊗ g + ⊢ g +
+-cons g = id ,⊗ +→* g

*-singleton : (g : Grammar ℓG) → g ⊢ g *
*-singleton g = CONS ∘g id ,⊗ NIL ∘g ⊗-unit-r⁻
