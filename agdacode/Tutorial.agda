module Tutorial where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : A → List A → List A

infixr 20 _∷_

data Vec {a} (A : Set a) : ℕ → Set a where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

data Even : ℕ → Set where
  z-even : Even zero
  s-even : ∀ {n} → Even n → Even (suc (suc n))

six : ℕ
six = suc (suc (suc (suc (suc (suc zero)))))

6-even : Even six
6-even = s-even (s-even (s-even z-even))

data dummy {a b} : Set a → Set b where

_+_ : ℕ → ℕ → ℕ
zero    + b = b
(suc a) + b = suc (a + b)

size : ∀ {a} {A : Set a} → List A → ℕ
size []        = zero
size (hd ∷ tl) = suc (size tl)

myList : List ℕ
myList = zero ∷ []

sizeImp : ℕ
sizeImp = size myList

sizeExp : ℕ
sizeExp = size {A = ℕ} myList

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]        ++ l = l
(hd ∷ tl) ++ l = hd ∷ (tl ++ l)

data _≡_ {a} {A : Set a} (x : A) : A → Set where
  refl : x ≡ x

cong : ∀ {a b} {A : Set a} {B : Set b} {x y} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

≡size : ∀ {a} {A : Set a} {l l₁ : List A} → (size l + size l₁) ≡ size (l ++ l₁)
≡size {l = []} = refl
≡size {l = hd ∷ tl} = cong suc (≡size {l = tl})

_++̬_ : ∀ {n n₁ a} {A : Set a} → Vec A n → Vec A n₁ → Vec A (n + n₁)
[] ++̬ v₂ = v₂
(x ∷ v₁) ++̬ v₂ = x ∷ (v₁ ++̬ v₂)

data ⊥ : Set where

¬ : ∀ {a} → Set a → Set a
¬ A = A → ⊥

data Dec {a} (A : Set a) : Set a where
  yes : (p : A) → Dec A
  no  : (¬p : ¬ A) → Dec A

dec≡ : ∀ {x y : ℕ} → Dec (x ≡ y)
dec≡ {zero}  {zero}  = yes refl
dec≡ {zero}  {suc y} = no (λ ())
dec≡ {suc x} {zero}  = no (λ ())
dec≡ {suc x} {suc y} with dec≡ {x} {y}
dec≡ {suc x} {suc y} | yes x≡y = yes (cong suc x≡y)
dec≡ {suc x} {suc y} | no ¬x≡y = no (λ {refl → (¬x≡y refl)})
