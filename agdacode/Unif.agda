module Unif where

open import Relation.Binary.PropositionalEquality

trans≡ : ∀ {a} {A : Set a} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
trans≡ {x = x} {.x} {.x} refl refl = refl

cong≡ : ∀ {a b} {A : Set a} {B : Set b} {x y} →
  (f : A → B) → x ≡ y → f x ≡ f y
cong≡ {x = x} {.x} f refl = refl

