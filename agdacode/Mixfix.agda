module Mixfix where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data List : Set where
  ∅ : List
  _↪_ : ℕ → List → List

zeros : List
zeros = zero ↪ (zero ↪ (zero ↪ ∅)) 

