open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (sym to sym≡ ; trans to trans≡ ; refl to refl≡)
open import Relation.Unary
open import Data.Empty
open import Agda.Primitive
open import Data.Sum
open import Relation.Nullary
open import Data.Product
open import Data.Unit
open import Function
open import Relation.Nullary.Negation
open import Helper

module Instant (Instant : StrictPartialOrder lzero lzero lzero) where

open StrictPartialOrder renaming (_≈_ to _≋_)
open IsStrictPartialOrder
open IsEquivalence

Support : Set
Support = Carrier Instant

_≺_ : Rel Support lzero
_≺_ = _<_ Instant

_≈_ : Rel Support lzero
_≈_ = _≋_ Instant

_≼_ : Rel Support lzero
x ≼ y = x ≈ y ⊎ x ≺ y

_≠_ : Rel Support lzero
x ≠ y = x ≺ y ⊎ y ≺ x

_∥_ : Rel Support lzero
x ∥ y = ¬ x ≠ y × ¬ x ≈ y

_≺'_ : ∀ {u} {P Q : Pred Support u} → REL (∃ P) (∃ Q) _
_≺'_ = proj₁ -⟦ _≺_ ⟧- proj₁

_≼'_ : ∀ {u} {P Q : Pred Support u} → REL (∃ P) (∃ Q) _
_≼'_ = proj₁ -⟦ _≼_ ⟧- proj₁

_≈'_ : ∀ {u} {P Q : Pred Support u} → REL (∃ P) (∃ Q) _
_≈'_ = proj₁ -⟦ _≈_ ⟧- proj₁

_≠'_ : ∀ {u} {P Q : Pred Support u} → REL (∃ P) (∃ Q) _
_≠'_ = proj₁ -⟦ _≠_ ⟧- proj₁

_∥'_ : ∀ {u} {P Q : Pred Support u} → REL (∃ P) (∃ Q) _
_∥'_ = proj₁ -⟦ _∥_ ⟧- proj₁

_≡'_ : ∀ {u} {P Q : Pred Support u} → REL (∃ P) (∃ Q) _
_≡'_ = proj₁ -⟦ _≡_ ⟧- proj₁

private
  ispo : IsStrictPartialOrder _≈_ _≺_
  ispo = isStrictPartialOrder Instant

irrefl≈≺ : Irreflexive _≈_ _≺_
irrefl≈≺ = irrefl ispo

trans≺ : Transitive _≺_
trans≺ = trans ispo

private
  ≺-resp-≈ : _≺_ Respects₂ _≈_
  ≺-resp-≈ = <-resp-≈ ispo

≺-resp-≈₁ : ∀ {x} → (x ≺_) Respects _≈_
≺-resp-≈₁ = proj₁ ≺-resp-≈

≺-resp-≈₂ : ∀ {x} → (_≺ x) Respects _≈_
≺-resp-≈₂ = proj₂ ≺-resp-≈

private
  ie : IsEquivalence _≈_
  ie = isEquivalence ispo

refl≈ : Reflexive _≈_
refl≈ = refl ie

sym≈ : Symmetric _≈_
sym≈ = sym ie

trans≈ : Transitive _≈_
trans≈ = trans ie

sym≠ : Symmetric _≠_
sym≠ (inj₁ x) = inj₂ x
sym≠ (inj₂ y) = inj₁ y

sym∥ : Symmetric _∥_
sym∥ (u , v) = u ∘ sym≠ , v ∘ sym≈

toSetoid : ∀ {u} (P : Pred Support u) → Setoid _ _
toSetoid P = record {
  Carrier = ∃ P ; _≈_ = _≈'_ ;
  isEquivalence = record { refl = refl≈ ; sym = sym≈ ; trans = trans≈}}

≺→¬≈ : ∀ {x y} → x ≠ y → ¬ x ≈ y
≺→¬≈ (inj₁ x≺y) x≈y = irrefl≈≺ x≈y x≺y
≺→¬≈ (inj₂ y≺x) x≈y = irrefl≈≺ (sym≈ x≈y) y≺x

antisym≼ : Antisymmetric _≈_ _≼_
antisym≼ (inj₁ x) _ = x
antisym≼ _ (inj₁ x) = sym≈ x
antisym≼ {α} (inj₂ α≺β) (inj₂ β≺α) = contradiction
  (trans≺ α≺β β≺α) (irrefl≈≺ (refl≈ {α}))

trans≼ : Transitive _≼_
trans≼ (inj₁ i≈j) (inj₁ j≈k) = inj₁ (trans≈ i≈j j≈k)
trans≼ (inj₁ i≈j) (inj₂ j≺k) = inj₂ (≺-resp-≈₂ (sym≈ i≈j) j≺k)
trans≼ (inj₂ i≺j) (inj₁ j≈k) = inj₂ (≺-resp-≈₁ j≈k i≺j)
trans≼ (inj₂ i≺j) (inj₂ j≺k) = inj₂ (trans≺ i≺j j≺k)

refl≼ : Reflexive _≼_ ; refl≼ = inj₁ refl≈

trans≺≼ : ∀ {α β γ} → α ≺ β → β ≼ γ → α ≺ γ
trans≺≼ α≺β (inj₁ β≈γ) = ≺-resp-≈₁ β≈γ α≺β
trans≺≼ α≺β (inj₂ β≺γ) = trans≺ α≺β β≺γ

trans≼≺ : ∀ {α β γ} → α ≼ β → β ≺ γ → α ≺ γ
trans≼≺ (inj₁ α≈β) β≺γ = ≺-resp-≈₂ (sym≈ α≈β) β≺γ
trans≼≺ (inj₂ α≺β) β≺γ = trans≺ α≺β β≺γ

≼→¬≺ : ∀ {α β} → α ≼ β → ¬ β ≺ α
≼→¬≺ (inj₁ α≈β) β≺α = irrefl≈≺ (sym≈ α≈β) β≺α
≼→¬≺ (inj₂ α≺β) β≺α = ≺→¬≈ (inj₂ (trans≺ β≺α α≺β)) refl≈

≼→¬≺→≈ : ∀ {α β} → α ≼ β → ¬ α ≺ β → α ≈ β
≼→¬≺→≈ (inj₁ α≈β) _ = α≈β
≼→¬≺→≈ (inj₂ α≺β) ¬α≺β = ⊥-elim (¬α≺β α≺β)

¬⊎→×¬ : ∀ {a} {A B : Set a} → ¬ (A ⊎ B) → ¬ A × ¬ B
¬⊎→×¬ ¬a⊎b = ¬a⊎b ∘ inj₁ , ¬a⊎b ∘ inj₂

∥→≈→∥₁ : ∀ {α β γ} → α ∥ β → β ≈ γ → α ∥ γ
∥→≈→∥₁ {α} {β} (¬α≠β , ¬α≈β) β≈γ with ¬⊎→×¬ ¬α≠β
∥→≈→∥₁ (_ , ¬α≈β) β≈γ | ¬α≺β , ¬β≺α
  = (λ { (inj₁ α≺γ) → ¬α≺β (≺-resp-≈₁ (sym≈ β≈γ) α≺γ) ;
         (inj₂ γ≺α) → ¬β≺α (≺-resp-≈₂ (sym≈ β≈γ) γ≺α)})
    , (λ α≈γ → ¬α≈β (trans≈ α≈γ (sym≈ β≈γ)))

∥→≈→∥₂ : ∀ {α β γ} → α ∥ β → α ≈ γ → γ ∥ β
∥→≈→∥₂ α∥β α≈γ = sym∥ (∥→≈→∥₁ (sym∥ α∥β) α≈γ)

≺≈≈→≺ : ∀ {α β γ δ} → α ≺ β → α ≈ γ → β ≈ δ → γ ≺ δ
≺≈≈→≺ α≺β α≈γ β≈δ = ≺-resp-≈₂ α≈γ (≺-resp-≈₁ β≈δ α≺β)

≼≈≈→≼ : ∀ {α β γ δ} → α ≼ β → α ≈ γ → β ≈ δ → γ ≼ δ
≼≈≈→≼ (inj₁ α≈β) α≈γ β≈δ =
  inj₁ (trans≈ (sym≈ α≈γ) (trans≈ α≈β β≈δ))
≼≈≈→≼ (inj₂ α≺β) α≈γ β≈δ =
  inj₂ (≺≈≈→≺ α≺β α≈γ β≈δ)

≼-resp-≈₁ : ∀ {x} → (x ≼_) Respects _≈_
≼-resp-≈₁ x₁≈y (inj₁ x≈x₁) = inj₁ (trans≈ x≈x₁ x₁≈y)
≼-resp-≈₁ x₁≈y (inj₂ x≺x₁) = inj₂ (≺-resp-≈₁ x₁≈y x≺x₁)

≼-resp-≈₂ : ∀ {x} → (_≼ x) Respects _≈_
≼-resp-≈₂ x₁≈y (inj₁ x₁≈x) = inj₁ (trans≈ (sym≈ x₁≈y) x₁≈x)
≼-resp-≈₂ x₁≈y (inj₂ x₁≼x) = inj₂ (≺-resp-≈₂ x₁≈y x₁≼x)

≡→≈ : ∀ {i j} → i ≡ j → i ≈ j
≡→≈ _≡_.refl = refl≈
