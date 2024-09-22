{- An LR(0) grammar and parser for Tuples -}

{- Grammar for one associative binary operation with constants and parens -}
module Examples.Tuple where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe as Maybe
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Sigma

data Tok : Type where
  LP RP : Tok   -- left and right parens
  COMMA : Tok   -- comma
  num : ℕ → Tok -- constants

Alphabet : hSet _
Alphabet = Tok , isSetRetract encode decode dex≡x (isSet⊎ isSetFin isSetℕ)
  where
  open import Cubical.Data.Sum as Sum
  open import Cubical.Data.Fin as Fin
  Tok' : Type _
  Tok' = Fin 3 ⊎ ℕ
  encode : Tok → Tok'
  encode LP = inl 0
  encode RP = inl 1
  encode COMMA = inl 2
  encode (num x) = inr x
  decode : Tok' → Tok
  decode (inl (0 , snd₁)) = LP
  decode (inl (1 , snd₁)) = RP
  decode (inl (suc (suc fst₁) , snd₁)) = COMMA
  decode (inr x) = num x
  dex≡x : ∀ x → decode (encode x) ≡ x
  dex≡x LP = refl
  dex≡x RP = refl
  dex≡x COMMA = refl
  dex≡x (num x) = refl

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Term Alphabet

anyNum : Grammar _
anyNum = LinΣ[ n ∈ ℕ ] literal (num n)

module Tree where
  data Tuple : Grammar ℓ-zero
  data List : Grammar ℓ-zero
  data Tuple where
    atom : anyNum ⊢ Tuple
    tuple : literal LP ⊗ List ⊗ literal RP ⊢ Tuple
  data List where -- Alt definition (maybe better?) Tuple ⊗ KL* (literal Comma ⊗ Tuple)
    done : Tuple ⊢ List
    more : List ⊗ literal COMMA ⊗ Tuple ⊢ List

-- What do I actually need in my LR state for the parser?
--
-- I know that a fully reduced state looks like a sequence of "frames" ( L ,
-- ( L , ( L , ... ( L , followed by either ε or ( or ( L
--
-- A frame is either
-- ( L , or just (

module Automaton where
  Stack = ℕ
  data Frame : Type where
    LP LPList LPListComma : Frame
  data State : Type where
    Start Done : State
    Working : Stack → Frame → State

  -- First just the accepting traces
  data Trace : State → Grammar ℓ-zero where
    done : ε ⊢ Trace Done

    lp-start : literal LP ⊗ Trace (Working 0 LP) ⊢ Trace Start
    lp-push-lp    : ∀ {stk} → literal LP ⊗ Trace (Working (suc stk) LP) ⊢ Trace (Working stk LP)
    lp-push-comma : ∀ {stk} → literal LP ⊗ Trace (Working (suc stk) LP) ⊢ Trace (Working stk LPListComma)

    comma : ∀ {stk} → literal COMMA ⊗ Trace (Working stk LPListComma) ⊢ Trace (Working stk LPList)

    num-first : ∀ {stk} → anyNum ⊗ Trace (Working stk LPList) ⊢ Trace (Working stk LP)
    num-next  : ∀ {stk} → anyNum ⊗ Trace (Working stk LPList) ⊢ Trace (Working stk LPListComma)

    rp-done : literal RP ⊗ Trace Done ⊢ Trace (Working zero LPList)
    rp-more : ∀ {stk} → literal RP ⊗ Trace (Working stk LPList) ⊢ Trace (Working (suc stk) LPList)

module Soundness where
  mkTree : Automaton.Trace Automaton.Start ⊢ Tree.Tuple
  mkTree = {!!} where
    -- We construct this as an algebra of the Trace signature.
    [Stack] : Automaton.Stack → Grammar ℓ-zero
    [Stack] 0       = ε
    [Stack] (suc n) = [Stack] n ⊗ literal LP ⊗ KL* (Tree.Tuple ⊗ literal COMMA) 
    [Frame] : Automaton.Frame → Grammar ℓ-zero
    [Frame] Automaton.LP = literal LP
    [Frame] Automaton.LPList = literal LP ⊗ Tree.List
    [Frame] Automaton.LPListComma = literal LP ⊗ Tree.List ⊗ literal COMMA
    Motive : Automaton.State → Grammar ℓ-zero
    Motive Automaton.Start = Tree.Tuple
    Motive Automaton.Done = ε
    Motive (Automaton.Working stk frame) = ([Stack] stk ⊗ [Frame] frame) ⊸ Tree.Tuple

    [done] : ε ⊢ Motive Automaton.Done
    [done] = id

    [lp-start] : literal LP ⊗ Motive (Automaton.Working 0 Automaton.LP) ⊢ Motive Automaton.Start
    [lp-start] = {!!} -- ok

    [lp-push-lp] : ∀ {stk} → literal LP ⊗ Motive (Automaton.Working (suc stk) Automaton.LP) ⊢ Motive (Automaton.Working stk Automaton.LP)
    [lp-push-lp] = {!!} -- shoudl work

    [lp-push-comma] : ∀ {stk} → literal LP ⊗ Motive (Automaton.Working (suc stk) Automaton.LP) ⊢ Motive (Automaton.Working stk Automaton.LPListComma)
    [lp-push-comma] = {!!} -- if we can Tree.List ⊗ literal COMMA ⊢ KL* (Tree.Tuple ⊗ literal COMMA)

    [comma] : ∀ {stk} → literal COMMA ⊗ Motive (Automaton.Working stk Automaton.LPListComma) ⊢ Motive (Automaton.Working stk Automaton.LPList)
    [comma] = {!!}

    [num-first] : ∀ {stk} → anyNum ⊗ Motive (Automaton.Working stk Automaton.LPList) ⊢ Motive (Automaton.Working stk Automaton.LP)
    [num-first] = {!!} --ok 
    [num-next]  : ∀ {stk} → anyNum ⊗ Motive (Automaton.Working stk Automaton.LPList) ⊢ Motive (Automaton.Working stk Automaton.LPListComma)
    [num-next] = {!!} -- ok

    [rp-done] : literal RP ⊗ Motive Automaton.Done ⊢ Motive (Automaton.Working zero Automaton.LPList)
    [rp-done] = {!!} -- ok
    [rp-more] : ∀ {stk} → literal RP ⊗ Motive (Automaton.Working stk Automaton.LPList) ⊢ Motive (Automaton.Working (suc stk) Automaton.LPList)
    [rp-more] = {!!} -- ok

    finish : Motive Automaton.Start ⊢ Tree.Tuple
    finish = id
