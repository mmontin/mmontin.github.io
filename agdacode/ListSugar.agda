open import Data.List
open import Data.Nat
open import Data.String

module ListSugar where

⟦_ : ∀ {a} {A : Set a} → List A → List A
⟦ l = l

_⟧ : ∀ {a} {A : Set a} → A → List A
a ⟧ = a ∷ []

_,_ : ∀ {a} {A : Set a} → A → List A → List A
a , l = a ∷ l

infixr 20 _,_
infix  15 ⟦_
infix  25 _⟧

example₁ : List ℕ
example₁ = ⟦ 2 , 3 , 4 ⟧

example₂ : List String
example₂ = ⟦ "hello" , "world" , "!" ⟧           

