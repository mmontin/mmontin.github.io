open import Data.Nat
open import Relation.Binary.PropositionalEquality

module Irrelevance where

data SList (bound : ℕ) : Set where
  []    : SList bound
  scons : (head : ℕ) →
         .(head ≤ bound) → -- note the dot!
          (tail : SList head) →
          SList bound

postulate
  5≤5₁ : 5 ≤ 5
  3≤5₁ : 3 ≤ 5
  0≤3₁ : 0 ≤ 3

private
  5≤5₂ : 5 ≤ 5
  5≤5₂ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  3≤5₂ : 3 ≤ 5
  3≤5₂ = s≤s (s≤s (s≤s z≤n))
  0≤3₂ : 0 ≤ 3
  0≤3₂ = z≤n

sl₁ : SList 5
sl₁ = scons 5 5≤5₁ (scons 3 3≤5₁ (scons 0 0≤3₁ []))

sl₂ : SList 5
sl₂ = scons 5 5≤5₂ (scons 3 3≤5₂ (scons 0 0≤3₂ []))

sl₁≡sl₂ : sl₁ ≡ sl₂
sl₁≡sl₂ = refl

