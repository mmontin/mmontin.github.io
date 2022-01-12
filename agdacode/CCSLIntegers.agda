module CCSLIntegers where

open import Data.Integer
open import Data.Integer.Properties
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Data.Nat hiding (_<_ ; _+_)
open import Data.Nat.Properties using (n<1+n)
open import Relation.Nullary
open import Data.Empty

open import CCSL
  (record { isStrictPartialOrder = <-isStrictPartialOrder })
open import Interval
  (record { isStrictPartialOrder = <-isStrictPartialOrder })

always : Clock
always = (λ _ → ⊤) ⌞ λ {(i , _) (j , _) → <-cmp i j}

x-1<x : ∀ z → - 1ℤ + z < z
x-1<x (+_ zero) = -<+
x-1<x +[1+ zero ] = +<+ (s≤s z≤n)
x-1<x +[1+ ℕ.suc n ] = +<+ (n<1+n (ℕ.suc n))
x-1<x (-[1+ zero ] ) = -<- (s≤s z≤n)
x-1<x (-[1+ ℕ.suc n ]) = -<- (n<1+n (ℕ.suc n))

preserves₀ : ∀ {i j} → i < j → - 1ℤ + i < - 1ℤ + j
preserves₀ {+_ zero} {.(+[1+ _ ])} (+<+ (s≤s m<n)) = -<+
preserves₀ {+[1+ zero ]} {.(+[1+ _ ])} (+<+ (s≤s m<n)) = +<+ m<n
preserves₀ {+[1+ ℕ.suc n ]} {.(+[1+ _ ])} (+<+ (s≤s m<n)) = +<+ m<n
preserves₀ { -[1+_] n} {.(-[1+ _ ])} (-<- n<m) = -<- (s≤s n<m)
preserves₀ { -[1+_] zero} {+_ zero} -<+ = -<- (s≤s z≤n)
preserves₀ { -[1+_] zero} {+[1+ n ]} -<+ = -<+
preserves₀ { -[1+_] (ℕ.suc n)} {+_ zero} -<+ = -<- (s≤s z≤n)
preserves₀ { -[1+_] (ℕ.suc n)} {+[1+ m ]} -<+ = -<+

dense₀ : ∀ {p i j} → - 1ℤ + i < p → p < - 1ℤ + j → ∃ \k → - 1ℤ + k ≡ p
dense₀ {+_ zero} {+_ n₁} {+_ n₂} u v = +[1+ zero ] , refl
dense₀ {+[1+ n ]} {+_ n₁} {+_ n₂} u v = +[1+ ℕ.suc n ] , refl
dense₀ { -[1+_] zero} {+_ n₁} {+_ n₂} u v = + zero , refl
dense₀ { -[1+_] (ℕ.suc n)} {+_ n₁} {+_ n₂} u v = -[1+ n ] , refl
dense₀ { -[1+_] zero} {+_ n₁} { -[1+_] n₂} u v = + zero , refl
dense₀ { -[1+_] (ℕ.suc n)} {+_ n₁} { -[1+_] n₂} u v = -[1+ n ] , refl
dense₀ {+_ n} { -[1+_] n₁} {+_ n₂} u v = +[1+ n ] , refl
dense₀ { -[1+_] zero} { -[1+_] n₁} {+_ n₂} u v = + zero , refl
dense₀ { -[1+_] (ℕ.suc n)} { -[1+_] n₁} {+_ n₂} u v = -[1+ n ] , refl
dense₀ { -[1+_] zero} { -[1+_] n₁} { -[1+_] n₂} u v = + zero , refl
dense₀ { -[1+_] (ℕ.suc n)} { -[1+_] n₁} { -[1+_] n₂} u v = -[1+ n ] , refl

all≺≺all : always ≺≺ always
all≺≺all = record
  { h = λ {(x , tt) → (- 1ℤ + x , tt)}
  ; congruent = λ {refl → refl}
  ; precedes = x-1<x ∘ proj₁
  ; preserves = preserves₀
  ; dense = λ { {i , tt} {j , tt} {p , tt} x y →
    case dense₀ {p} {i} {j} x y of
      λ {(z , p) → (z , tt) , p}}}

data Evenℕ : ℕ → Set where
  even0 : Evenℕ 0
  evenss : ∀ {n} → Evenℕ n → Evenℕ (ℕ.suc (ℕ.suc n))

Oddℕ : ℕ → Set
Oddℕ = ¬_ ∘ Evenℕ

data Even : ℤ → Set where
  even+ : ∀ {n} → Evenℕ n → Even (+ n)
  even-1+ : ∀ {n} → Evenℕ n → Even -[1+ ℕ.suc n ]

Odd : ℤ → Set
Odd = ¬_ ∘ Even

prop : ∀ {n} → Evenℕ n → Oddℕ (ℕ.suc n)
prop {.0} even0 = λ ()
prop {.(ℕ.suc (ℕ.suc _))} (evenss p) (evenss q) = prop p q

-1change : ∀ {z} → Even z → Odd (- 1ℤ + z)
-1change {+[1+ .(ℕ.suc _) ]} (even+ (evenss x)) (even+ x₁) = prop x x₁
-1change { -[1+_] .(ℕ.suc _)} (even-1+ x) (even-1+ x₁) = prop x x₁

1-change : ∀ {z} → Odd z → Even (- 1ℤ + z)
1-change {+_ zero} p = ⊥-elim (p (even+ even0))
1-change {+[1+ zero ]} p = even+ even0
1-change {+[1+ ℕ.suc zero ]} p = ⊥-elim (p (even+ (evenss even0)))
1-change {+[1+ ℕ.suc (ℕ.suc n) ]} p
  with 1-change {+[1+ n ]} λ {(even+ x) → p (even+ (evenss x))}
1-change {+[1+ ℕ.suc (ℕ.suc n) ]} p | even+ x = even+ (evenss x)
1-change { -[1+_] zero} p = even-1+ even0
1-change { -[1+_] (ℕ.suc zero)} p = ⊥-elim (p (even-1+ even0))
1-change { -[1+_] (ℕ.suc (ℕ.suc n))} p
  with 1-change { -[1+ n ]} λ {(even-1+ x) → p (even-1+ (evenss x))}
1-change { -[1+_] (ℕ.suc (ℕ.suc n))} p | even-1+ x = even-1+ (evenss x)

change-1 : ∀ {z} → Odd (- 1ℤ + z) → Even z
change-1 {+_ zero} _ = even+ even0
change-1 {+[1+ zero ]} x = ⊥-elim (x (even+ even0))
change-1 {+[1+ ℕ.suc zero ]} x = even+ (evenss even0)
change-1 {+[1+ ℕ.suc (ℕ.suc n) ]} x
  with change-1 {+[1+ n ]} λ {(even+ y) → x (even+ (evenss y))}
change-1 {+[1+ ℕ.suc (ℕ.suc n) ]} x | even+ x₁ = even+ (evenss x₁)
change-1 { -[1+_] zero} x = ⊥-elim (x (even-1+ even0))
change-1 { -[1+_] (ℕ.suc zero)} x = even-1+ even0
change-1 { -[1+_] (ℕ.suc (ℕ.suc n))} x
  with change-1 { -[1+ n ]} λ {(even-1+ y) → x (even-1+ (evenss y))}
change-1 { -[1+_] (ℕ.suc (ℕ.suc .(ℕ.suc _)))} x
  | even-1+ x₁ = even-1+ (evenss x₁)

evenClock : Clock
evenClock = Even ⌞ λ {(x , _) (y , _) → <-cmp x y}

oddClock : Clock
oddClock = Odd ⌞ λ {(x , _) (y , _) → <-cmp x y}

e≺≺o : evenClock ≺≺ oddClock
e≺≺o = record { h = λ {(z , o) → (- 1ℤ + z , 1-change o)}
  ; congruent = λ {refl → refl}
  ; precedes = x-1<x ∘ proj₁
  ; preserves = preserves₀
  ; dense = λ { {i , oi} {j , oj} {p , op} x y → case dense₀ {p} {i} {j} x y
    of λ {(z , refl) → (z , (flip -1change) op) , refl}}}

o≺≺e : oddClock ≺≺ evenClock
o≺≺e = record { h = λ {(z , o) → (- 1ℤ + z , -1change o)}
  ; congruent = λ {refl → refl}
  ; precedes = x-1<x ∘ proj₁
  ; preserves = preserves₀
  ; dense = λ { {i , oi} {j , oj} {p , op} x y → case dense₀ {p} {i} {j} x y
    of λ {(z , refl) → (z , change-1 op) , refl}}}

¬e∼o : ¬ evenClock ∽ oddClock
¬e∼o (e⊑o , o⊑e) with e⊑o (0ℤ , even+ even0)
¬e∼o (e⊑o , o⊑e) | (.+0 , odd0) , refl = odd0 (even+ even0)
