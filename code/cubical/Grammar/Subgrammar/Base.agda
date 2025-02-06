open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

module Grammar.Subgrammar.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List hiding (rec ; map)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Unit
import Cubical.Data.Empty as Empty

open import Grammar Alphabet
open import Grammar.Inductive.Indexed Alphabet hiding (k)
-- open import Grammar.Base Alphabet
-- open import Grammar.LinearProduct Alphabet
-- open import Grammar.Epsilon Alphabet
-- open import Grammar.Inductive.Indexed Alphabet hiding (k)
-- open import Grammar.Dependent.Base Alphabet

open import Term Alphabet

private
  variable
    ℓg ℓh ℓk ℓl ℓ ℓ' : Level
    g g' g'' g1 g2 g3 g4 g5 : Grammar ℓg
    h h' h'' : Grammar ℓh
    k : Grammar ℓk
    f f' f'' : g ⊢ h
    l : Grammar ℓl

Ω : Grammar (ℓ-suc ℓ)
Ω {ℓ = ℓ} w = hProp ℓ

opaque
  unfolding ⊤
  true : ⊤ ⊢ Ω {ℓ = ℓ}
  true w x .fst = Unit*
  true w x .snd = isPropUnit*

  false : ⊤ ⊢ Ω {ℓ = ℓ}
  false w x .fst = Empty.⊥*
  false w x .snd = Empty.isProp⊥*

-- A subgrammar is a subobject in the category of grammars
-- Intuitively,
-- if a grammar g is a map from strings to sets of parses,
-- a subgrammar is map that picks out
-- a subset of parses for each string
--
-- More precisely, we'll handle these by means of
-- the subobject classifier. i.e. a subgrammar of g
-- is uniquely identified by a morphism from
-- g to Ω
--
-- It isn't clear to me how to best expose this syntactically in
-- the language
-- We could just add in constructs to the language like we did
-- with equalizers, although I'm not sure if we'd need to restrict
-- the type of propositions of not
-- For instance, in the cases we care about, we could just
-- restrict the language of propositions you can perform the
-- following constructions on to be something like
--    - the proposition that two maps are equal, recovering
--      the definition of equalizers
--    - the proposition that some grammar is uninhabited. For example
--      you could take the subgrammar of g that doesn't start
--      with the character c
--      -  which would be the subgrammar over the proposition
--         that g & (＂ c ＂ ⊗ ⊤) ⊢ ⊥
module _ {ℓ} {g : Grammar ℓg} (p : g ⊢ Ω {ℓ = ℓ}) where
  opaque
    unfolding ⊤ true
    subgrammar : Grammar (ℓ-max ℓg ℓ)
    subgrammar w = Σ[ x ∈ g w ] ⟨ p w x ⟩

    sub-π : subgrammar ⊢ g
    sub-π w = fst

    sub-π-pf : p ∘g sub-π ≡ true ∘g ⊤-intro
    sub-π-pf = funExt (λ w → funExt λ x →
      Σ≡Prop
        (λ _ → isPropIsProp)
        (hPropExt (p w (x .fst) .snd) (true w _ .snd)
          _
          λ _ → x .snd)
      )

  module _
    (f : h ⊢ g)
    (ph : p ∘g f ≡ true ∘g ⊤-intro) where
    opaque
      unfolding subgrammar
      sub-intro : h ⊢ subgrammar
      sub-intro w x .fst = f w x
      sub-intro w x .snd =
        transport
          (sym (cong fst (funExt⁻ (funExt⁻ ph w) x)))
          tt*

      sub-β : sub-π ∘g sub-intro ≡ f
      sub-β = refl

  module _
    (f : h ⊢ subgrammar)
    where
    opaque
      unfolding subgrammar sub-intro
      private
        the-path : p ∘g sub-π ∘g f ≡ true ∘g ⊤-intro
        the-path = cong (_∘g f) sub-π-pf

      sub-η :
        f
          ≡
        sub-intro
          (sub-π ∘g f)
          the-path  -- writing "the-path" here works but
                    -- cong (_∘g f) sub-π-pf is a weird levels error.
                    -- Not quite sure why
      sub-η i = f

  -- if you can build a section, then p holds over all of
  -- g
  -- the statement "p ≡ true ∘g ⊤-intro" means
  -- semantically ∀ w → (x : g w) → ⟨ p w x ⟩
  -- i.e. that p holds for each g parse
  subgrammar-section :
    (f : g ⊢ subgrammar) →
    (sub-π ∘g f ≡ id) →
    p ≡ true ∘g ⊤-intro
  subgrammar-section f sec =
    cong (p ∘g_) (sym sec)
    ∙ cong (_∘g f) sub-π-pf
    ∙ cong (true ∘g_) (unambiguous⊤ _ _)

module _
  {A : Type ℓ} (F : A → Functor A) (g : A → Grammar ℓg)
  (p : ∀ (a : A) → μ F a ⊢ Ω {ℓ = ℓ})
  (pf : ∀ (a : A) →
    p a ∘g roll ∘g map (F a) (λ a' → sub-π (p a'))
      ≡
    true ∘g ⊤-intro
  )
  where

  subgrammar-ind-alg : Algebra F (λ a → subgrammar (p a))
  subgrammar-ind-alg a =
    sub-intro
      (p a)
      (roll ∘g map (F a) (λ a' → sub-π (p a')))
      (pf a)

  sub-π-homo :
    Homomorphism F subgrammar-ind-alg (initialAlgebra F)
  sub-π-homo .fst a = sub-π (p a)
  sub-π-homo .snd a = is-homo
    where
    opaque
      unfolding sub-π sub-intro
      is-homo :
        sub-π (p a) ∘g subgrammar-ind-alg a
        ≡
        initialAlgebra F a ∘g map (F a) (λ a' → sub-π (p a'))
      is-homo = refl

  subgrammar-ind : ∀ (a : A) → p a ≡ true ∘g ⊤-intro
  subgrammar-ind a =
    subgrammar-section
      (p a)
      (rec F subgrammar-ind-alg a)
      (ind-id'
        F
        (compHomo F
          (initialAlgebra F)
          subgrammar-ind-alg
          (initialAlgebra F)
          sub-π-homo
          (recHomo F subgrammar-ind-alg)
        )
        a
      )
