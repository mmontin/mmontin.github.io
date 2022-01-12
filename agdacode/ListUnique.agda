open import Relation.Binary renaming (Decidable to Decidable)
open import Relation.Binary.PropositionalEquality
open import ListConform
open import Function

module ListUnique {a} (A : Set a) (decA : Decidable {A = A} _≡_) where
    open FunctionRelation {B = A} id
    open GlobalUnicity _≡f_ renaming (GUList to Bag) public
    open Commands {B = A} id decA id
      hiding (elementsF ; elementsG)
      renaming (elementsId to elements ; newGUL to newBag) public
