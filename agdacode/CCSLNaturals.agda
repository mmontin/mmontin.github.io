open import Data.Nat hiding (compare)
open import Data.Nat.Induction
open import Data.Nat.Properties 
open import Relation.Binary hiding (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary hiding (_⇒_)
open import Relation.Nullary
open import Data.Product
open import Function
open import Data.Empty
open import Data.Sum renaming (swap to swap⊎)
open import Relation.Nullary.Negation
open import Induction.WellFounded

module CCSLNaturals where

precedent : ∀ {ℓ} {P : Pred ℕ ℓ} → Decidable P → (j : ∃ P) →
  (∀ {x} → x < proj₁ j → ¬ P x) ⊎ ∃ \(i : ∃ P)
    → proj₁ i < proj₁ j × (∀ {x} → proj₁ i < x → x < proj₁ j → ¬ P x)
precedent _ (zero , _) = inj₁ \()
precedent dp (suc j , tj) = aux dp j (suc j) tj (n<1+n _)
  λ j<x → ⊥-elim ∘ (<-irrefl {suc j} refl) ∘ (<-transʳ j<x) where
    aux : ∀ {ℓ} {P : Pred ℕ ℓ} (dp : Decidable P)
      (i j : ℕ) (pc : P j) (i<j : i < j) →
      (∀ {x} → i < x → x < j → ¬ P x)
      → (∀ {x} → x < j → ¬ P x) ⊎
      ∃ \(k : ∃ P) → proj₁ k < j ×
      (∀ {x} → proj₁ k < x → x < j → ¬ P x)
    aux dp i j pc i≺j p with dp i
    aux dp zero j pc i≺j p | no ¬p = inj₁ λ {
      {zero} x<j tx → ⊥-elim (¬p tx) ;
      {suc _} x<j tx → p (s≤s z≤n) x<j tx}
    aux dp (suc i) j pc i≺j p | no ¬p =
      aux dp i j pc (<-trans (n<1+n i) i≺j)
        λ i<x x<j tx → case m≤n⇒m<n∨m≡n i<x of
          λ {(inj₁ si<x) → p si<x x<j tx ; (inj₂ refl) → ¬p tx}
    aux dp i j pc i≺j p | yes p₁ = inj₂ ((i , p₁) , i≺j , p)

wf-<P : ∀ {ℓ} {P : Pred ℕ ℓ} → Decidable P
  → WellFounded {A = ∃ P} (_<_ on proj₁)
wf-<P {P = P} dec x = aux x (<-wellFounded (proj₁ x))
  where
    aux : ∀ (i : ∃ P) → Acc _<_ (proj₁ i) → Acc (_<_ on proj₁) i
    aux i ai with precedent dec i
    aux i ai | inj₁ p = acc (λ j j≺i → ⊥-elim (p j≺i (proj₂ j)))
    aux i (acc q) | inj₂ (j , j≺i , p) with aux j (q _ j≺i)
    aux i ai | inj₂ (j , j≺i , p) | acc rs =
      acc λ y y≺i → case <-cmp (proj₁ j) (proj₁ y) of λ {
        (tri< a _ _) → ⊥-elim ((p a y≺i) (proj₂ y)) ;
        (tri≈ _ refl _) → acc rs ;
        (tri> _ _ c) → rs y c}

initial : ∀ {ℓ} {P : Pred ℕ ℓ} → Decidable P
  → ∃ P → ∃ λ (x : ∃ P) → ∀ (y : ∃ P) → proj₁ x ≤ proj₁ y
initial {P = P} dec p = aux p (<-wellFounded _)
  where
    aux : (i : ∃ P) → Acc _<_ (proj₁ i) →
      ∃ λ (x : ∃ P) → ∀ (y : ∃ P) → proj₁ x ≤ proj₁ y
    aux i (acc p) with precedent dec i
    aux i (acc p) | inj₁ x = i , λ y →
      case <-cmp (proj₁ i) (proj₁ y) of λ {
        (tri< a _ _) → <⇒≤ a ;
        (tri≈ _ refl _) → ≤-refl ;
        (tri> _ _ c) → ⊥-elim (x c (proj₂ y))}
    aux i (acc p) | inj₂ (y , z , _) = aux y (p _ z)

open import CCSL
  (record {
    isStrictPartialOrder = <-isStrictPartialOrder })
open Clock

record Clock-¬∅-Dec : Set₁ where
  field
    clock : Clock
    non-empty : ∃ (Ticks clock)
    decidable : Decidable (Ticks clock)

  wf-≺ : _
  wf-≺ = wf-<P decidable

  birth : _
  birth = let (i , p) = initial decidable non-empty in
    i , swap⊎ ∘ m≤n⇒m<n∨m≡n ∘ p

  toWf : WFClock
  toWf = record { clock = clock ; wf-≺ = wf-≺ }

  toIn : InitialClock
  toIn = record { clock = clock ; first = birth }

