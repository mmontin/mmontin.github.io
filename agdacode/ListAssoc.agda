open import Relation.Binary renaming (Decidable to Decidableᵣ)
open import Relation.Binary.PropositionalEquality
open import ListConform
open import Function
open import Data.Product

module ListAssoc {a} (A : Set a)
  (decA : Decidableᵣ {A = A} _≡_) {b} {B : Set b} where
  open FunctionRelation {B = A × B} proj₁
  open GlobalUnicity _≡f_ renaming (GUList to Map) public
  open Commands {B = A × B} proj₁ decA proj₂ renaming
    (elementsF to keys ; elementsG to values ; newGUL to newMap) public
