module Unary where

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Function
open import Agda.Primitive

data Even : ℕ → Set where
  zpair : Even zero
  spair : ∀ {a} → Even a → Even (suc (suc a))

record ∃ {a b} {A : Set a} (P : A → Set b) : Set (a ⊔ b) where
  constructor _,_ ; field
    witness : A
    proof   : P witness

Evenℕ : Set
Evenℕ = ∃ Even

[_/2] : Evenℕ → ℕ
[ .zero , zpair /2] = zero
[ .(suc (suc _)) , spair proof /2] = suc [ _ , proof /2]

_≈_ : ∀ {a b} {A : Set a} {P : A → Set b} → Rel (∃ P) _
_≈_ =  _≡_ on ∃.witness

uniqueEven : ∀ {n} (p₁ p₂ : Even n) → p₁ ≡ p₂
uniqueEven zpair      zpair      = refl
uniqueEven (spair p₁) (spair p₂) = cong spair (uniqueEven p₁ p₂)

equality : ∀ {e₁ e₂ : ∃ Even} → e₁ ≈ e₂ → e₁ ≡ e₂
equality {_ , p} {._ , p₁} refl rewrite uniqueEven p p₁ = refl
