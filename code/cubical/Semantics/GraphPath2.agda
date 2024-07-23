module Semantics.GraphPath2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum hiding (elim ; rec ; map)
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥ hiding (elim ; rec)
open import Cubical.Data.Unit
open import Cubical.Data.Nat as Nat hiding (elim)
import      Cubical.Data.Nat.Order.Recursive as NatOrd
open import Cubical.Data.SumFin as SumFin hiding (finj ; fsuc ; elim)
open import Cubical.Data.SumFin.More
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Cubical.Data.Graph
open import Cubical.Data.Graph.Displayed

open import Semantics.Helper

private
  variable
    ℓ ℓ' : Level

module _
  (G : Graph ℓ ℓ')
  (isFinSetNode : isFinSet (G .Graph.Node))
  where

  open Graph G

  --PathWithNodes : 

