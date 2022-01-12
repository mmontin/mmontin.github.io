module ListSize where

open import Data.List
open import Data.Nat

lsize : ∀ {a} {A : Set a} → List A → ℕ
lsize [] = 0
lsize (x ∷ l) = suc (lsize l)

open import Relation.Binary.PropositionalEquality

sl₀+sl₁≡sl₀++l₁ : ∀ {a} {A : Set a} {l₀ l₁ : List A} → lsize l₀ + lsize l₁ ≡ lsize (l₀ ++ l₁)
sl₀+sl₁≡sl₀++l₁ {l₀ = []} = refl
sl₀+sl₁≡sl₀++l₁ {l₀ = x ∷ l₀} = cong suc (sl₀+sl₁≡sl₀++l₁ {l₀ = l₀})

_×_ : ∀ {a} {A : Set a} → ℕ → List A → List A
zero × l = []
suc n × l = l ++ (n × l)

sn×l≡n*sl : ∀ {a} {A : Set a} {l : List A} {n} → lsize (n × l) ≡ n * (lsize l)
sn×l≡n*sl {n = zero} = refl
sn×l≡n*sl {l = l} {suc n} = trans (sym (sl₀+sl₁≡sl₀++l₁ {l₀ = l} {l₁ = n × l})) (cong (λ x → lsize l + x) (sn×l≡n*sl {n = n}))
