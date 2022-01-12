open import Data.Nat
open import Relation.Binary.PropositionalEquality

module Commut where

n≡n+0 : ∀ {b} → b ≡ b + 0
n≡n+0 {zero} = refl
n≡n+0 {suc b} = cong suc n≡n+0

s[b+n]≡b+s[n] : ∀ {b n} → suc (b + n) ≡ b + suc n
s[b+n]≡b+s[n] {zero} = refl
s[b+n]≡b+s[n] {suc n} = cong suc s[b+n]≡b+s[n]

comm : ∀ {a b} → a + b ≡ b + a
comm {zero} = n≡n+0
comm {suc a} = trans (cong suc (comm {a})) s[b+n]≡b+s[n]

