open import Relation.Binary.Bundles
open import Relation.Binary.Structures
open import Agda.Primitive
open import Data.Product
open import Function.Base
open import Function.Equality hiding (_∘_ ; const ; flip)
open import Function.Bijection hiding (_∘_)
open import Function.Injection hiding (_∘_)
open import Relation.Binary
open import Data.String
open import ListAssoc String _≟_
open import Data.List.Relation.Unary.Any renaming (Any to Anyₗ)
open import Data.Maybe.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Relation.Unary renaming (Decidable to Decidableₚ) hiding (_∈_)
open import Relation.Nullary
open import Data.Empty
open import Data.String.Properties
open import Data.List.Membership.Setoid Data.String.Properties.≡-setoid
open import Data.Nat hiding (_⊔_)

module Helper where

imageSetoid : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
  (f : A ⟶ B) → Setoid (a₁ ⊔ b₁ ⊔ b₂) b₂
imageSetoid {B = record {
  Carrier = _ ; _≈_ = _≈_ ;
  isEquivalence = record { refl = r ; sym = s ; trans = t }}}
  record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } = record {
    Carrier = ∃ λ y → ∃ (y ≈_ ∘ _⟨$⟩_) ;
    _≈_ = _≈_ on proj₁ ;
    isEquivalence = record { refl = r ; sym = s ; trans = t } }

imageFunction : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
  (f : A ⟶ B) → (A ⟶ imageSetoid f)
imageFunction {B = B} record { _⟨$⟩_ = f ; cong = cong } =
  let refl≈ = IsEquivalence.refl (Setoid.isEquivalence B) in
  record {
    _⟨$⟩_ = λ x → f x , x , refl≈ ;
    cong = cong }

injtobij : ∀ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} {f} →
  Injective {A = A} {B} f → Bijective (imageFunction f)
injtobij {B = record { Carrier = Carrier ; _≈_ = _ ;
  isEquivalence = record { refl = _ ; sym = s ; trans = t }}} inj = record {
  injective = inj ; surjective = record {
    from = record {
      _⟨$⟩_ = proj₁ ∘ proj₂ ;
      cong = λ { {_ , _ , y} {_ , _ , z} → inj ∘ t (s y) ∘ flip t z}} ;
    right-inverse-of = s ∘ proj₂ ∘ proj₂ }}

_-⟦_⟧-_ : ∀ {a b c d e}
  {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e}
  → (A → B) → (B → D → E) → (C → D) → (A → C → E)
f -⟦ _*_ ⟧- g = (λ x _ → f x) -[ _*_ ]- λ _ z → g z

infix 20 _-⟦_⟧-_

_>[_]>_ : ∀ {ℓ} {I : Set} {P P' Q : Pred I ℓ}
  {R : Rel I ℓ}
  (v : ∃ λ (j : ∃ P) → (Q ∘ proj₁) j)
  (p : ∀ {j k} → Q j → R k j → Q k)
  (h : ∀ (x : ∃ P) → ∃ λ (y : ∃ P') → R (proj₁ y) (proj₁ x)) →
  ∃ λ (j : ∃ P') → (Q ∘ proj₁) j
_>[_]>_ (v , Qv) p h with h v
_>[_]>_ (v , Qv) p h | w , Rwv = w , p Qv Rwv

infixl 5 _>[_]>_

getp : ∀ {x} {ℓ b} {B : Set b} {P : Pred B ℓ} {m : Map {B = B}}
  → Any P (get x m) → x ∈ₗ m
getp {x} {m = m} _ with dec∈ₗ x m
getp {x} {m = m} p | yes q = q

sub : ∀ {a b} → a ≤ b → ℕ
sub (z≤n {n}) = n
sub (s≤s p) = sub p

prop← : ∀ {ℓ} {B : Set ℓ} {m : Map {B = B}} {x}
  → x ∈ₗ m → x ∈ (keys m)
prop← (here px) = here px
prop← {m = m} (there p) = there (prop← {m = trim m λ {()}} p)

fromSample : ∀ {a ℓ} {A : Set a} {P : Pred A ℓ} (l : List A) →
  Decidableₚ P → (∀ {x} → ¬ Anyₗ (x ≡_) l → ¬ P x) → Dec (∃ P)
fromSample [] _ q = no λ {(_ , px) → q (λ {()}) px}
fromSample (x ∷ _) decp _ with decp x
fromSample (x ∷ _) _ _ | yes p = yes (x , p)
fromSample (x ∷ l) decp q | no ¬p = fromSample l decp λ ¬avl pv →
  q (λ {(here refl) → ⊥-elim (¬p pv) ; (there avl) → ¬avl avl}) pv

∃P×Q→∃P : ∀ {a b c} {A : Set a} {P : Pred A b} {Q : A → Set c}
  → ∃ (P ∩ Q) → ∃ P
∃P×Q→∃P (v , Pv , _) = v , Pv

∃!→∃ : ∀ {a b ℓ} {A : Set a} {P : A → Set b} {_≈_}
  → ∃! {ℓ = ℓ} _≈_ P → ∃ P
∃!→∃ = ∃P×Q→∃P
