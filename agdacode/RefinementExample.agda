open import Data.Nat.DivMod
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function
open import Relation.Binary
open import Data.Product
open import Relation.Unary
open import Relation.Nullary
open import Data.Empty

module RefinementExample where

open import Refinement
open import Data.Sum renaming (inj₁ to l ; inj₂ to r)

_≈₂_ : _
_≈₂_ = _≡_ on _div 5

eq≈₂ : IsEquivalence _≈₂_
eq≈₂ = record { refl = refl ; sym = sym ; trans = trans }

_≺₂_ : _
_≺₂_ = _<_ on _div 5

irr≺₂≈₂ : Irreflexive _≈₂_ _≺₂_
irr≺₂≈₂ {x} {y} with x div 5 | y div 5
irr≺₂≈₂ | suc _ | suc _ = <-irrefl

resp≺₂≈₂ : _≺₂_ Respects₂ _≈₂_
resp≺₂≈₂ = (λ { {x} {y} {z} → aux₁ {x} {y} {z}}) ,
  λ { {x} {y} {z} → aux₂ {x} {y} {z}}
  where
    aux₁ : ∀ {x y z} → y ≈₂ z → x ≺₂ y → x ≺₂ z
    aux₁ {x} {y} {z} with x div 5 | y div 5 | z div 5
    aux₁ | _ | _ | _ = proj₁ (resp₂ _<_)
    aux₂ : ∀ {x y z} → y ≈₂ z → y ≺₂ x → z ≺₂ x
    aux₂ {x} {y} {z} with x div 5 | y div 5 | z div 5
    aux₂ | _ | _ | _ = proj₂ (resp₂ _<_)

ispo≈₂≺₂ : IsStrictPartialOrder _≈₂_ _≺₂_
ispo≈₂≺₂ = record {
  isEquivalence = eq≈₂ ;
  irrefl = λ { {x} {y} → irr≺₂≈₂ {x} {y}} ;
  trans = <-trans ;
  <-resp-≈ = resp≺₂≈₂ }

_≈₁_ : Rel ℕ _
a ≈₁ b = (a / 5) ≡ (b / 5) × (a % 5 ≡ b % 5 ⊎ a % 5 + b % 5 ≡ 1)

sym≈₁ : Symmetric _≈₁_
sym≈₁ {a} {b} (fst , snd) with a / 5 | b / 5 | a % 5 | b % 5
sym≈₁ {a} {b} (fst , l x) | _ | _ | _ | _ = (sym fst) , l (sym x)
sym≈₁ {a} {b} (fst , r y) | _ | _ | w | w₁ =
  (sym fst) , r (trans (+-comm w₁ w) y)

trans≈₁ : Transitive _≈₁_
trans≈₁ {a} {b} {c} _ _ with a / 5 | b / 5 | c / 5 | a % 5 | b % 5 | c % 5
trans≈₁ (refl , l refl) (refl , l refl) | _ | _ | _ | _ | _ | _ = refl , l refl
trans≈₁ (refl , l refl) (refl , r y) | _ | _ | _ | _ | _ | _ = refl , r y
trans≈₁ (refl , r y) (refl , l refl) | _ | _ | _ | _ | _ | _ = refl , r y
trans≈₁ (refl , r refl) (refl , r refl) | _ | _ | _ | zero | .1 | .0 = refl , l refl
trans≈₁ (refl , r refl) (refl , r refl) | _ | _ | _ | suc zero | .0 | .1 = refl , l refl

eq≈₁ : IsEquivalence _≈₁_
eq≈₁ = record {
  refl = refl , l refl ;
  sym = λ { {a} {b} → sym≈₁ {a} {b}};
  trans = λ { {a} {b} {c} → trans≈₁ {a} {b} {c} }}

_≺₁_ : Rel ℕ _
a ≺₁ b = a / 5 < b / 5 ⊎ (a / 5 ≡ b / 5 × a % 5 < b % 5 × ¬ b % 5 ≡ 1)

trans≺₁ : Transitive _≺₁_
trans≺₁ {a} {b} {c} _ _ with a / 5 | b / 5 | c / 5 | a % 5 | b % 5 | c % 5
trans≺₁ (l x) (l x₁) | _ | _ | _ | _ | _ | _ = l (<-trans x x₁)
trans≺₁ (l x) (r (refl , _)) | _ | _ | _ | _ | _ | _ = l x
trans≺₁ (r (refl , _)) (l x) | _ | _ | _ | _ | _ | _ = l x
trans≺₁ (r (refl , u , _)) (r (refl , w , x)) | _ | _ | _ | _ | _ | _ =
  r (refl , (<-trans u w , x))

irr≈₁≺₁ : Irreflexive _≈₁_ _≺₁_
irr≈₁≺₁ {a} {b} _ _ with a / 5 | b / 5 | a % 5 | b % 5
irr≈₁≺₁ (refl , snd) (l (s≤s x)) | _ | _ | _ | _ = <-irrefl refl x
irr≈₁≺₁ (refl , l refl) (r (refl , fst , _)) | _ | _ | _ | _ = <-irrefl refl fst
irr≈₁≺₁ (refl , r y₁) (r (refl , _ , snd)) | _ | _ | zero | _ = snd y₁
irr≈₁≺₁ (refl , r refl) (r (refl , () , snd)) | _ | _ | suc zero | _

resp≺≈₁ᵣ : _≺₁_ Respectsʳ _≈₁_
resp≺≈₁ᵣ {a} {b} {c} _ _ with a / 5 | b / 5 | c / 5 | a % 5 | b % 5 | c % 5
resp≺≈₁ᵣ (refl , _) (l x) | _ | _ | _ | _ | _ | _ = l x
resp≺≈₁ᵣ (refl , l refl) (r y) | _ | _ | _ | _ | _ | _ = r y
resp≺≈₁ᵣ (refl , r refl) (r (refl , _ , snd)) | _ | _ | _ | _ | suc zero | .0 =
  ⊥-elim (snd refl)

resp≺≈₁ₗ : _≺₁_ Respectsˡ _≈₁_
resp≺≈₁ₗ {a} {b} {c} _ _ with a / 5 | b / 5 | c / 5 | a % 5 | b % 5 | c % 5
resp≺≈₁ₗ (refl , _) (l x) | _ | _ | _ | _ | _ | _ = l x
resp≺≈₁ₗ (refl , l refl) (r y) | _ | _ | _ | _ | _ | _ = r y
resp≺≈₁ₗ (refl , r refl) (r (refl , fst , snd)) | _ | _ | _ | suc _ | zero | .1 =
  r (refl , ≤∧≢⇒< fst (snd ∘ sym) , snd)
resp≺≈₁ₗ (refl , r refl) (r (refl , _ , snd)) | _ | _ | _ | suc _ | suc zero | _ =
  r (refl , s≤s z≤n , snd)

resp≺₁≈₁ : _≺₁_ Respects₂ _≈₁_
resp≺₁≈₁ =
  (λ { {x} {y} {z} → resp≺≈₁ᵣ {x} {y} {z}}) ,
  λ { {x} {y} {z} → resp≺≈₁ₗ {x} {y} {z}}

ispo≈₁≺₁ : IsStrictPartialOrder _≈₁_ _≺₁_
ispo≈₁≺₁ = record {
  isEquivalence = eq≈₁ ;
  irrefl = λ { {x} {y} → irr≈₁≺₁ {x} {y}} ;
  trans = λ { {x} {y} {z} → trans≺₁ {x} {y} {z}} ;
  <-resp-≈ = resp≺₁≈₁ }

aux₁ : ∀ {a b} → a ≺₁ b → a ≺₂ b ⊎ a ≈₂ b
aux₁ {a} {b} _ with a / 5 | b / 5 | a % 5 | b % 5
aux₁ (l x) | _ | _ | _ | _ = l x
aux₁ (r (refl , _)) | _ | _ | _ | _ = r refl

aux₂ : ∀ {a b} → a ≈₂ b → a ≈₁ b ⊎ a ≺₁ b ⊎ b ≺₁ a
aux₂ {a} {b} _ with a / 5 | b / 5 | a % 5 | b % 5
aux₂ refl | _ | _ | zero | zero = l (refl , l refl)
aux₂ refl | _ | _ | zero | suc zero = l (refl , r refl)
aux₂ refl | _ | _ | zero | suc (suc _) = r (l (r (refl , s≤s z≤n , (λ ()))))
aux₂ refl | _ | _ | suc zero | zero = l (refl , r refl)
aux₂ refl | _ | _ | suc (suc _) | zero = r (r (r (refl , s≤s z≤n , (λ ()))))
aux₂ refl | _ | _ | suc zero | suc zero = l (refl , l refl)
aux₂ refl | _ | _ | suc zero | suc (suc _) =
  r (l (r (refl , s≤s (s≤s z≤n) , (λ ()))))
aux₂ refl | _ | _ | suc (suc w) | suc zero =
  r (r (r (refl , s≤s (s≤s z≤n) , (λ ()))))
aux₂ refl | _ | _ | suc (suc w) | suc (suc w₁) with <-cmp w w₁
aux₂ refl | _ | _ | suc (suc _) | suc (suc _) | tri< a _ _ =
  r (l (r (refl , s≤s (s≤s a) , (λ ()))))
aux₂ refl | _ | _ | suc (suc _) | suc (suc ._) | tri≈ _ refl _ =
  l (refl , l refl)
aux₂ refl | _ | _ | suc (suc _) | suc (suc _) | tri> _ _ c =
  r (r (r (refl , s≤s (s≤s c) , (λ ()))))

refines : (_≈₁_ , _≺₁_) ≺≈ (_≈₂_ , _≺₂_)
refines = record {
  ≈₁→₂ = proj₁ ;
  ≈₂→₁ = λ { {a} {b} → aux₂ {a} {b}} ;
  ≺₁→₂ = λ { {a} {b} → aux₁ {a} {b}} ;
  ≺₂→₁ = l }
