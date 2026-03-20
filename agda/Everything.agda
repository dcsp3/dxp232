module Everything where

-- Prelude
open import Prelude

-- Syntax
open import Syntax.Syntax
open import Syntax.Decidable
open import Syntax.ExampleTodoAPI

-- Well-formedness
open import WellFormed.Core
open import WellFormed.IllFormed
open import WellFormed.Decidable

-- Semantics
open import Semantics.Variance

open import Semantics.SchemaRefinement
open import Semantics.EndpointRefinement
open import Semantics.APIRefinement

open import Semantics.SchemaRefinementProperties
open import Semantics.EndpointRefinementProperties
open import Semantics.APIRefinementProperties

open import Semantics.Drift
open import Semantics.DriftProperties
open import Semantics.Compatibility
open import Semantics.DecidableRefinement
