open import Relation.Binary
open import Relation.Unary
open import Agda.Primitive
open import Data.Product
open import Relation.Nullary
open import Data.Sum hiding (map₂)
open import Function

module Interval (Inst : StrictPartialOrder lzero lzero lzero) where

open import Instant Inst public

data Interval : Set where
  ⟦_-_⟧ : (α β : Support) → Interval
  ⟦_-∞⟦ : (α : Support) → Interval

_∈ᵢ_ : Support → Interval → Set
v ∈ᵢ ⟦ α -∞⟦ = α ≼ v
v ∈ᵢ ⟦ α - β ⟧ = α ≼ v × ¬ (β ≺ v)

inf : Interval → Support
inf ⟦ α - _ ⟧ = α
inf ⟦ α -∞⟦ = α

_⊂ᵢ_ : Rel Interval _
I ⊂ᵢ J = (_∈ᵢ I) ⊆ (_∈ᵢ J)

≈∈ : ∀ {i₁ i₂ I} → i₁ ≈ i₂ → i₁ ∈ᵢ I → i₂ ∈ᵢ I
≈∈ {I = ⟦ α - β ⟧} i₁≈i₂ (α≼i₁ , ¬β≺i₁)
  = ≼-resp-≈₁ i₁≈i₂ α≼i₁ ,
    (λ β≺i₂ → ¬β≺i₁ (≺-resp-≈₁ (sym≈ i₁≈i₂) β≺i₂))
≈∈ {I = ⟦ α -∞⟦} i₁≈i₂ (inj₁ α≈i₁) = inj₁ (trans≈ α≈i₁ i₁≈i₂)
≈∈ {I = ⟦ α -∞⟦} i₁≈i₂ (inj₂ α≺i₁) = inj₂ (≺-resp-≈₁ i₁≈i₂ α≺i₁)

trans⊂ : Transitive _⊂ᵢ_
trans⊂ u v = v ∘ u

sameB : ∀ {i j k} → j ≈ k → i ∈ᵢ ⟦ j - k ⟧ → i ≈ j
sameB j≈k = sym≈ ∘ (uncurry ≼→¬≺→≈) ∘ map₂ (_∘ (≺-resp-≈₂ j≈k))
