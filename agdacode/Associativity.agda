module Associativity where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixr 20 _↪_

data List : Set where
  ∅ : List
  _↪_ : ℕ → List → List

zeros : List
zeros = zero ↪ zero ↪ zero ↪ ∅

infixl 30 _++_

_++_ : List → List → List
∅ ++ l₁ = l₁
(x ↪ l) ++ l₁ = x ↪ l ++ l₁

