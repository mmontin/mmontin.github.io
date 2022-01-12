module IfThenElse where

data Boolean : Set where
  ⊤ : Boolean
  ⊥ : Boolean

if_then_else_ : ∀ {a} {A : Set a} → Boolean → A → A → A
if ⊤ then a₁ else _  = a₁
if ⊥ then _  else a₂ = a₂

