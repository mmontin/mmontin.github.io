open import Data.Sum
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Construct.Union
open import Agda.Primitive
open import Function
open import Relation.Binary.PropositionalEquality

module Refinement {a} {I : Set a} where

record Transform {ℓ} (≈₁ ≈₂ ≺₁ ≺₂ : Rel I ℓ)
  (T≈₁₂ T≈₂₁ T≺₁₂ T≺₂₁ : _ → _ → Rel I ℓ) : Set (lsuc a ⊔ ℓ) where
  field
     ≈₁→₂ : ≈₁ ⇒ T≈₁₂ ≈₂ ≺₂
     ≈₂→₁ : ≈₂ ⇒ T≈₂₁ ≈₁ ≺₁
     ≺₁→₂ : ≺₁ ⇒ T≺₁₂ ≈₂ ≺₂
     ≺₂→₁ : ≺₂ ⇒ T≺₂₁ ≈₁ ≺₁

open Transform public

_≈≈_ : ∀ {ℓ} → Rel (Rel I ℓ × Rel I ℓ) _
(≈₁ , ≺₁) ≈≈ (≈₂ , ≺₂) = Transform ≈₁ ≈₂ ≺₁ ≺₂
    (λ ≈₂ _ → ≈₂)
    (λ ≈₁ _ → ≈₁)
    (λ _ ≺₂ → ≺₂)
    (λ _ ≺₁ → ≺₁)

_≺≈_ : ∀ {ℓ} → Rel (Rel I ℓ × Rel I ℓ) _
(≈₁ , ≺₁) ≺≈ (≈₂ , ≺₂) = Transform ≈₁ ≈₂ ≺₁ ≺₂
    (λ ≈₂ _ → ≈₂)
    (λ ≈₁ ≺₁ → ≈₁ ∪ (≺₁ ∪ flip ≺₁))
    (λ ≈₂ ≺₂ → ≺₂ ∪ ≈₂)
    (λ _ ≺₁ → ≺₁)

refl≈≈ : ∀ {ℓ} → Reflexive (_≈≈_ {ℓ})
refl≈≈ = record
  { ≺₁→₂ = id ; ≺₂→₁ = id ; ≈₁→₂ = id ; ≈₂→₁ = id }

sym≈≈ : ∀ {ℓ} → Symmetric (_≈≈_ {ℓ})
sym≈≈ x≈≈y .≈₁→₂ = ≈₂→₁ x≈≈y
sym≈≈ x≈≈y .≈₂→₁ = ≈₁→₂ x≈≈y
sym≈≈ x≈≈y .≺₁→₂ = ≺₂→₁ x≈≈y
sym≈≈ x≈≈y .≺₂→₁ = ≺₁→₂ x≈≈y

trans≈≈ : ∀ {ℓ} → Transitive (_≈≈_ {ℓ})
trans≈≈ i≈≈j j≈≈k .≈₁→₂ = (≈₁→₂ j≈≈k) ∘ ≈₁→₂ i≈≈j
trans≈≈ i≈≈j j≈≈k .≈₂→₁ = (≈₂→₁ i≈≈j) ∘ ≈₂→₁ j≈≈k
trans≈≈ i≈≈j j≈≈k .≺₁→₂ = (≺₁→₂ j≈≈k) ∘ ≺₁→₂ i≈≈j
trans≈≈ i≈≈j j≈≈k .≺₂→₁ = (≺₂→₁ i≈≈j) ∘ ≺₂→₁ j≈≈k

equiv≈≈ : ∀ {ℓ} → IsEquivalence (_≈≈_ {ℓ})
equiv≈≈ = record { refl = refl≈≈ ; sym = sym≈≈ ; trans = trans≈≈ }

trans≺≈ : ∀ {ℓ} → Transitive (_≺≈_ {ℓ})
trans≺≈ i≺≈j j≺≈k .≈₁→₂ = (≈₁→₂ j≺≈k) ∘ ≈₁→₂ i≺≈j
trans≺≈ i≺≈j j≺≈k .≈₂→₁ x with ≈₂→₁ j≺≈k x
trans≺≈ i≺≈j _ .≈₂→₁ _ | inj₁ y = ≈₂→₁ i≺≈j y
trans≺≈ i≺≈j _ .≈₂→₁ _ | inj₂ (inj₁ y) = inj₂ (inj₁ (≺₂→₁ i≺≈j y))
trans≺≈ i≺≈j _ .≈₂→₁ _ | inj₂ (inj₂ y) = inj₂ (inj₂ (≺₂→₁ i≺≈j y))
trans≺≈ i≺≈j _ .≺₁→₂ x with ≺₁→₂ i≺≈j x
trans≺≈ _ j≺≈k .≺₁→₂ _ | inj₁ y = ≺₁→₂ j≺≈k y
trans≺≈ _ j≺≈k .≺₁→₂ _ | inj₂ y = inj₂ (≈₁→₂ j≺≈k y)
trans≺≈ i≺≈j j≺≈k .≺₂→₁ = (≺₂→₁ i≺≈j) ∘ ≺₂→₁ j≺≈k

refl≺≈ : ∀ {ℓ} → (_≈≈_ {ℓ}) ⇒ (_≺≈_ {ℓ})
refl≺≈ i≈≈j .≈₁→₂ = ≈₁→₂ i≈≈j
refl≺≈ i≈≈j .≈₂→₁ = inj₁ ∘ ≈₂→₁ i≈≈j
refl≺≈ i≈≈j .≺₁→₂ = inj₁ ∘ ≺₁→₂ i≈≈j
refl≺≈ i≈≈j .≺₂→₁ = ≺₂→₁ i≈≈j

preorder≺≈≈ : ∀ {ℓ} → IsPreorder _≈≈_ (_≺≈_ {ℓ})
preorder≺≈≈ = record {
  isEquivalence = equiv≈≈ ;
  reflexive = refl≺≈ ;
  trans = trans≺≈ }

antisym≺≈ : ∀ {ℓ} → Antisymmetric _≈≈_ (_≺≈_ {ℓ})
antisym≺≈ i≺≈j _ .≈₁→₂ = ≈₁→₂ i≺≈j
antisym≺≈ _ j≺≈i .≈₂→₁ = ≈₁→₂ j≺≈i
antisym≺≈ _ j≺≈i .≺₁→₂ = ≺₂→₁ j≺≈i
antisym≺≈ i≺≈j _ .≺₂→₁ = ≺₂→₁ i≺≈j

partialOrder≺≈≈ : ∀ {ℓ} → IsPartialOrder _≈≈_ (_≺≈_ {ℓ})
partialOrder≺≈≈ = record {
  isPreorder = preorder≺≈≈ ;
  antisym = antisym≺≈ }
