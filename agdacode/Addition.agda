module Addition where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality
open import Function
open import Relation.Binary.PropositionalEquality.Core
open ≡-Reasoning

_+_ : ℕ → ℕ → ℕ
zero + b = b
suc a + b = suc (a + b)

associative+ : ∀ {a b c} → (a + b) + c ≡ a + (b + c)
associative+ {zero} = refl
associative+ {suc a} = cong suc (associative+ {a})

commutative+ : ∀ {a b} → a + b ≡ b + a
commutative+ {zero} = +0
  where
    +0 : ∀ {a} → a ≡ a + zero
    +0 {zero} = refl
    +0 {suc _} = cong suc +0
commutative+ {suc a} = trans (cong suc (commutative+ {a})) +suc
  where
    +suc : ∀ {a b} → suc (a + b) ≡ a + suc b
    +suc {zero} = refl
    +suc {suc _} = cong suc +suc

_*_ : ℕ → ℕ → ℕ
zero * b = zero 
suc a * b = b + (a * b)

distributive* : ∀ {a b c} → (a + b) * c ≡ (a * c) + (b * c)
distributive* {zero} = refl
distributive* {suc a} {b} {c} = trans (cong (c +_) (distributive* {a}))
  (sym (associative+ {c} {a * c} {b * c}))

associative* : ∀ {a b c} → a * (b * c) ≡ (a * b) * c
associative* {zero} = refl
associative* {suc a} {b} {c} rewrite distributive* {b} {a * b} {c}
  | sym (associative* {a} {b} {c}) = refl

*0 : ∀ {a} → a * 0 ≡ 0
*0 {zero} = refl
*0 {suc a} = *0 {a}

*suc : ∀ {a b} → a * suc b ≡ a + (a * b)
*suc {zero} = refl
*suc {suc a} {b} = cong suc (begin
  b + (a * suc b) ≡⟨ cong (b +_) (*suc {a} {b}) ⟩
  b + (a + (a * b)) ≡˘⟨ associative+ {b} {a} {a * b} ⟩
  (b + a) + (a * b) ≡⟨ cong (_+ (a * b)) (commutative+ {b} {a}) ⟩
  (a + b) + (a * b) ≡⟨ associative+ {a} {b} {a * b} ⟩
  a + (b + (a * b)) ∎)

commutative* : ∀ {a b} → a * b ≡ b * a
commutative* {zero} {b} = sym (*0 {b})
commutative* {suc a} {b} = begin
  (b + (a * b)) ≡⟨ cong (b +_) (commutative* {a}) ⟩
  (b + (b * a)) ≡˘⟨ *suc {b} ⟩
  (b * suc a) ∎

2+5≡7 : 2 + 5 ≡ 7
2+5≡7 = refl

2+5≡7₁ : 2 + 5 ≡ 7
2+5≡7₁ = begin 2 + 5 ≡⟨⟩ 1 + 6 ≡⟨⟩ 7 ∎ 

45*89 : 3 * 45 ≡ 135
45*89 = begin 3 * 45 ≡⟨⟩ (45 + (2 * 45)) ≡⟨⟩ (45 + (45 + 45)) ≡⟨⟩ 135 ∎
