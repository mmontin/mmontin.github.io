module ListConform where

open import Data.List hiding (any ; length ; lookup ; zip) renaming (map to mapl)
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Char.Properties
open import Data.String.Base hiding (_<_)
open import Data.String hiding (_<_)
open import Data.Sum hiding (swap ; map₂ ; map₁)
open import Data.Product
open import Data.Empty
open import Data.Fin renaming (suc to fsuc) hiding (_≤_ ; _<_)
open import Data.Fin.Properties renaming (suc-injective to fsuc-injective)
open import Data.Nat hiding (_⊔_ ; _≤_ ; _<_)
open import Data.Maybe hiding (zip ; _>>=_)
open import Data.Maybe.Properties
open import Data.Maybe.Categorical
open import Data.List.Relation.Unary.Any renaming (map to mapAny)
open import Agda.Primitive
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Unary hiding (_∈_ ; _∉_ ; _⇒_) renaming (Decidable to Decidableₚ)
open import Relation.Binary renaming (Decidable to Decidableᵣ)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import ListSugar renaming (_,_ to _↪_)
open import Function hiding (_↪_)
open import Category.Monad

module AnyUnique where

  data Any! {a b} {A : Set a} (P : Pred A b) : Pred (List A) (a ⊔ b)
    where
      here!  : ∀ {x xs} → P x → ¬ Any P xs → Any! P (x ∷ xs)
      there! : ∀ {x xs} → ¬ P x → Any! P xs → Any! P (x ∷ xs)

  data _≤_ : Rel ℕ lzero where
    z≤n : ∀ {n} → zero  ≤ n
    s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

  _<_ : Rel ℕ _
  m < n = suc m ≤ n

  3< : Any! (_< 3) (⟦ 5 ↪ 2 ↪ 3 ⟧)
  3< = there!  (λ {(s≤s (s≤s (s≤s ())))}) (here! (s≤s (s≤s (s≤s z≤n)))
    λ {(here (s≤s (s≤s (s≤s ())))) ; (there ())})

  s≡5 : Any! ((_≡ 5) ∘ length) (⟦ "one" ↪ "two" ↪ "three" ⟧)
  s≡5 = there! (λ ()) (there! (λ ()) (here! refl λ ()))

  private
    variable

      a b : Level
      A : Set a
      P : Pred A b
      x : A
      l : List A

  A!→A : Any! P l → Any P l
  A!→A (here! x₁ _   ) = here x₁
  A!→A (there! _ any₁) = there (A!→A any₁)

  P→A→¬A! : P x → Any P l → ¬ Any! P (x ∷ l)
  P→A→¬A! _ apl (here! _ ¬apl) = ¬apl apl
  P→A→¬A! px _ (there! ¬px _) = ¬px px

  ¬P→¬A!→¬A! : ¬ P x → ¬ Any! P l → ¬ Any! P (x ∷ l)
  ¬P→¬A!→¬A! ¬px _ (here! px _) = ¬px px
  ¬P→¬A!→¬A! _ ¬a!pl (there! _ a!pl) = ¬a!pl a!pl

  ¬A!→P→¬A : Any! P (x ∷ l) → P x → ¬ Any P l
  ¬A!→P→¬A (here! _ ¬apl) _ = ¬apl
  ¬A!→P→¬A (there! ¬px _) px _ = ¬px px

  ¬P→¬A→¬A : ¬ P x → ¬ Any P l → ¬ Any P (x ∷ l)
  ¬P→¬A→¬A ¬px _ (here px) = ¬px px
  ¬P→¬A→¬A _ ¬apl (there apxl) = ¬apl apxl

  ¬A[] : ¬ Any P []
  ¬A[] ()

  infixr 1 ¬P→¬A→¬A
  syntax ¬P→¬A→¬A ¬px ¬apl = ¬px ↦ ¬apl

  syntax P→A→¬A! yRx w₂ = yRx ¬! w₂

  decAny! : Decidableₚ P → Decidableₚ (Any! P)
  decAny! _ [] = no (λ ())
  decAny! decP (x ∷ _) with decP x
  decAny! decP (_ ∷ l) | yes _ with (any decP) l
  decAny! _ _ | yes px | yes apl = no (P→A→¬A! px apl)
  decAny! _ _ | yes px | no ¬apl = yes (here! px ¬apl)
  decAny! decP (_ ∷ l) | no ¬px with decAny! decP l
  decAny! _ _ | no ¬px | yes a!pl = yes (there! ¬px a!pl)
  decAny! _ _ | no ¬px | no ¬a!pl = no (¬P→¬A!→¬A! ¬px ¬a!pl)

open AnyUnique

module Membership {a b c} {A : Set a} {B : Set b} (_R_ : REL A B c) where

  _∈_ : REL A (List B) _
  x ∈ xs = Any (x R_) xs
  
  _∈!_ : REL A (List B) _
  x ∈! xs = Any! (x R_) xs

  _∉_ : REL A (List B) _
  x ∉ xs = ¬ (x ∈ xs)
  
  _∉!_ : REL A (List B) _
  x ∉! xs = ¬ (x ∈! xs)

  dec∈ : Decidableᵣ _R_ → Decidableᵣ _∈_
  dec∈ = any ∘_

  dec∉ : Decidableᵣ _R_ → Decidableᵣ _∉_
  dec∉ dec x = ¬? ∘ (dec∈ dec x)

  dec∈! : Decidableᵣ _R_ → Decidableᵣ _∈!_
  dec∈! = decAny! ∘_

  dec∉! : Decidableᵣ _R_ → Decidableᵣ _∉!_
  dec∉! dec x = ¬? ∘ (dec∈! dec x)

module Examples where

  4<5 : 4 < 5
  4<5 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

  2<3 : 2 < 3
  2<3 = s≤s (s≤s (s≤s z≤n))

  2<5 : 2 < 5
  2<5 = s≤s (s≤s (s≤s z≤n))

  open Membership _<_ hiding (_∉_ ; _∈!_)
    renaming (_∈_ to _∈<_ ; _∉!_ to _∉!<_)

  list₁ : List ℕ
  list₁ = ⟦ 3 ↪ 5 ↪ 2 ⟧

  4∈list₁ : 4 ∈< list₁
  4∈list₁ = there (here 4<5)

  2∉!list₁ : 2 ∉!< list₁ -- 2 ∈!< list₁ → ⊥
  2∉!list₁ (here! _ ¬2∈<[5,2]) = ¬2∈<[5,2] (here 2<5) -- gives ⊥
  2∉!list₁ (there! ¬2<3 _) = ¬2<3 2<3 -- gives ⊥

  open import Data.List.Membership.Setoid Data.Char.Properties.≡-setoid

  _∈l_ : _ → _ → _ 
  c ∈l s = c ∈ toList s

  _∉l_ : _ → _ → _
  c ∉l s = c ∉ toList s

  z∉Alice : 'z' ∉l "Alice"
  z∉Alice = (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ ¬A[]

  z∉Bob : 'z' ∉l "Bob"
  z∉Bob = (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ ¬A[]

  z∉Judith : 'z' ∉l "Judith"
  z∉Judith = (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ ¬A[]

  J∉Alice : 'J' ∉l "Alice"
  J∉Alice = (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ ¬A[]

  J∉Bob : 'J' ∉l "Bob"
  J∉Bob = (λ ()) ↦ (λ ()) ↦ (λ ()) ↦ ¬A[]

  J∈Judith : 'J' ∈l "Judith"
  J∈Judith = here refl

  open Membership _∈l_ hiding (_∈_ ; _∉!_)
    renaming (_∉_ to _∉s_ ; _∈!_ to _∈!s_)

  list₂ : List String
  list₂ = ⟦ "Alice" ↪ "Bob" ↪ "Judith" ⟧

  z∉list₂ : 'z' ∉s list₂ -- 'z' ∉s list₂ → ⊥
  z∉list₂ (here z∈Alice) = z∉Alice z∈Alice -- gives ⊥
  z∉list₂ (there (here z∈Bob)) = z∉Bob z∈Bob -- gives ⊥
  z∉list₂ (there (there (here z∈Judith))) = z∉Judith z∈Judith -- gives ⊥
  z∉list₂ (there (there (there ()))) -- no such possible case

  z∉list₂' : 'z' ∉s list₂
  z∉list₂' = z∉Alice ↦ z∉Bob ↦ z∉Judith ↦ ¬A[]

  J∈!list₂ : 'J' ∈!s list₂
  J∈!list₂ = there! J∉Alice (there! J∉Bob (here! J∈Judith λ ()))

module GlobalUnicity {a b c} {A : Set a} {B : Set b} (_R_ : REL A B c) where
  open Membership _R_ 

  _∈∈!_ : REL _ _ _ -- Agda figures out the missing part
  x ∈∈! l = x ∈ l → x ∈! l

  Dec∈∈! : Decidableᵣ _R_ → Decidableᵣ _∈∈!_

  Dec∈∈! decR x l with dec∈! decR x l
  Dec∈∈! _ _ _ | yes p = yes (λ _ → p)
  Dec∈∈! decR x l | no _ with dec∈ decR x l
  Dec∈∈! _ _ _ | no ¬x∈!l | yes x∈l = no (λ x∈∈!l → ¬x∈!l (x∈∈!l x∈l))
  Dec∈∈! _ _ _ | no _ | no ¬x∈l = yes (λ x∈l → ⊥-elim (¬x∈l x∈l))

  GlobalUnicity : Pred _ _
  GlobalUnicity l = ∀ {x} → x ∈∈! l

  record GUList : Set (a ⊔ b ⊔ c) where
    constructor gulist
    field
      content : List B
      unique : GlobalUnicity content

  gu[a] : ∀ {a} → GlobalUnicity [ a ]
  gu[a] (here px) = here! px λ ()

  private
    variable

      x : B
      l : List B

  guTl : GlobalUnicity (x ∷ l) → GlobalUnicity l
  guTl guxl y∈l with guxl (there y∈l)
  guTl _ y∈l | here! _ y∉l = contradiction y∈l y∉l
  guTl _ y∈l | there! _ y∈!l = y∈!l

  _witnesses_ : _
  _witnesses_ = flip _R_

  _[witnesses]_ : _
  _[witnesses]_ = flip _∈_

  infix 10 _witnesses_
  infix 10 _[witnesses]_

  ≡index : _ → Set _
  ≡index l = ∀ {y} (w₁ w₂ : l [witnesses] y) → index w₁ ≡ index w₂

  ⇒ : GlobalUnicity l → ≡index l
  ⇒ _ (here _) (here _) = refl
  ⇒ gul (here yRx) (there w₂) = ⊥-elim ((yRx ¬! w₂) (gul (here yRx)))
  ⇒ gul (there w₁) (here yRx) = ⊥-elim ((yRx ¬! w₁) (gul (here yRx)))
  ⇒ gul (there w₁) (there w₂) = cong fsuc (⇒ (guTl gul) w₁ w₂)

  helper : ∀ {y} → ≡index (x ∷ l) → x witnesses y → ¬ l [witnesses] y
  helper ≡ind px x∈xs = case ≡ind (here px) (there x∈xs) of λ ()

  ⇐ : ≡index l → GlobalUnicity l
  ⇐ ≡ind (here px) = here! px (helper ≡ind px)
  ⇐ ≡ind (there x∈l) = there! (_⟨ helper ≡ind ⟩ x∈l)
    (⇐ (λ w₁ w₂ → fsuc-injective (≡ind (there w₁) (there w₂))) x∈l)

  _∷ᵤ_ : (∀ {y} → x witnesses y → ¬ l [witnesses] y)
    → GlobalUnicity l → GlobalUnicity (x ∷ l)
  _∷ᵤ_ p _ (here yRx) = here! yRx (p yRx)
  _∷ᵤ_ p gul (there y∈l) = there! (_⟨ p ⟩ y∈l) (gul y∈l)

  infixr 10 _∷ᵤ_ 

  gu[] : GlobalUnicity []
  gu[] ()

  gu[a]₀ : ∀ {a} → GlobalUnicity [ a ]
  gu[a]₀ = (λ {_ ()}) ∷ᵤ gu[]

module GlobalUnicityExample where
  open AnyUnique

  open GlobalUnicity {A = ℕ} _≡_

  l : List _
  l = ⟦ 3 ↪ 5 ↪ 2 ⟧  

  ¬⟦5,2⟧w3 : ∀ {y} → 3 witnesses y → ¬ ⟦ 5 ↪ 2 ⟧ [witnesses] y
  ¬⟦5,2⟧w3 refl = (λ ()) ↦ (λ ()) ↦ ¬A[]

  ¬⟦2⟧w5 : ∀ {y} → 5 witnesses y → ¬ ⟦ 2 ⟧ [witnesses] y
  ¬⟦2⟧w5 refl = (λ ()) ↦ ¬A[]

  ¬⟦⟧w2 : ∀ {y} → 2 witnesses y → ¬ [] [witnesses] y
  ¬⟦⟧w2 _ ()

  gul : GlobalUnicity l
  gul = ¬⟦5,2⟧w3 ∷ᵤ ¬⟦2⟧w5 ∷ᵤ ¬⟦⟧w2 ∷ᵤ gu[]

module GloballyUniqueEquivalence {a b} {A : Set a} {_≈_ : Rel A b}
  (isEq : IsEquivalence _≈_) where
  open GlobalUnicity _≈_
  open Membership _≈_ renaming (_∈_ to _∈≈_)

  open import Data.List.Membership.Setoid (record { Carrier = A ; _≈_ = _≡_ ; isEquivalence = isEquivalence })
  open Relation.Binary.PropositionalEquality.≡-Reasoning
  open IsEquivalence renaming (refl to ≈refl ; trans to ≈trans ; sym to ≈sym)

  ∈→∈≈ : ∀ {x l} → x ∈ l → x ∈≈ l
  ∈→∈≈ (here refl) = here (≈refl isEq)
  ∈→∈≈ (there x∈l) = there (∈→∈≈ x∈l)

  i≡ic : ∀ {x l} (p : x ∈ l) → index p ≡ index (∈→∈≈ p)
  i≡ic (here refl) = refl
  i≡ic (there p) = cong fsuc (i≡ic p)

  trans∈≈ : ∀ {x y l} → x ≈ y → x ∈≈ l → y ∈≈ l
  trans∈≈ x≈y (here px) = here (≈trans isEq (≈sym isEq x≈y) px)
  trans∈≈ x≈y (there x∈≈l) = there (trans∈≈ x≈y x∈≈l)

  it≡i : ∀ {x y l} (p : x ≈ y) (q : x ∈≈ l)
    → index (trans∈≈ p q) ≡ index q
  it≡i p (here px) = refl
  it≡i p (there q) = cong fsuc (it≡i p q)

  ≡i→≡ : ∀ {x y l} {x∈l : x ∈ l} {y∈l : y ∈ l}
    → index x∈l ≡ index y∈l → x ≡ y
  ≡i→≡ {x∈l = here refl} {here refl} refl = refl
  ≡i→≡ {x∈l = here px} {there y∈l} ()
  ≡i→≡ {x∈l = there x∈l} {here px} ()
  ≡i→≡ {x∈l = there x∈l} {there y∈l} u = ≡i→≡ (fsuc-injective u)

  gueq : ∀ {x y l} → x ∈ l → y ∈ l → GlobalUnicity l → x ≈ y → x ≡ y
  gueq x∈l y∈l gul x≈y = ≡i→≡ (begin
    index x∈l ≡⟨ i≡ic x∈l ⟩
    index (∈→∈≈ x∈l)
      ≡⟨ ⇒ gul (∈→∈≈ x∈l) (trans∈≈ (≈sym isEq x≈y) (∈→∈≈ y∈l)) ⟩
    index (trans∈≈ (≈sym isEq x≈y) (∈→∈≈ y∈l))
      ≡⟨ it≡i (≈sym isEq x≈y) (∈→∈≈ y∈l) ⟩
    index (∈→∈≈ y∈l) ≡˘⟨ i≡ic y∈l ⟩
    index y∈l ∎)

module GloballyUniqueTotalOrder {a b c} {A : Set a} {_≈_ : Rel A b}
  {_≼_ : Rel A c} (isTot : IsTotalOrder _≈_ _≼_) where
  open GlobalUnicity _≼_

  open IsEquivalence
  open IsTotalOrder

  ≼refl : ∀ {v} → v ≼ v
  ≼refl = IsPreorder.reflexive (IsPartialOrder.isPreorder (isPartialOrder isTot)) (IsEquivalence.refl (IsPreorder.isEquivalence (IsPartialOrder.isPreorder (isPartialOrder isTot))))

  prop : ∀ {l} → GlobalUnicity l → ¬ Data.List.length l > 1
  prop {[]} _ ()
  prop {_ ∷ []} _ (s≤s ())
  prop {x ∷ y ∷ _} _ with total isTot x y
  prop {_ ∷ _ ∷ _} gul | inj₁ x≼y =
    contradiction (gul (here ≼refl)) (P→A→¬A! ≼refl (here x≼y))
  prop {_ ∷ _ ∷ _} gul | inj₂ y≼x =
    contradiction (gul (there (here ≼refl))) (P→A→¬A! y≼x (here ≼refl))

  prop₂ : ∀ {l} → ¬ Data.List.length l > 1 → GlobalUnicity l
  prop₂ {[]} _ = gu[]
  prop₂ {_ ∷ []} _ = gu[a]
  prop₂ {_ ∷ _ ∷ _} p = case (p (s≤s (s≤s z≤n))) of λ ()

module FunctionRelation
  {a b} {A : Set a} {B : Set b} (f : B → A) where

  _≡f_ : REL A B a
  _≡f_ x = (x ≡_) ∘ f

  dec≡f : Decidableᵣ {A = A} _≡_ → Decidableᵣ _≡f_
  dec≡f dec x = (dec x) ∘ f

module Commands {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f : B → A) (dec : Decidableᵣ {A = A} _≡_) (g : B → C) where
  open FunctionRelation f
  open Membership _≡f_
  open GlobalUnicity _≡f_

  newGUL : GUList
  newGUL = gulist [] gu[]

  trim : (gul : GUList) → ¬ (GUList.content gul) ≡ [] → GUList
  trim (gulist [] unique) p = ⊥-elim (p refl)
  trim (gulist (_ ∷ content) unique) _ = gulist content (guTl unique)

  decGU : Decidableₚ GlobalUnicity
  decGU [] = yes gu[]
  decGU (x ∷ l) with dec∈ (dec≡f dec) (f x) l
  decGU _ | yes fx∈l =
    no (λ guxl → P→A→¬A! refl fx∈l (guxl (here refl)))
  decGU (x ∷ l) | no _ with decGU l
  decGU _ | no ¬fx∈l | yes gul =
    yes ((λ {refl fx∈l → ¬fx∈l fx∈l}) ∷ᵤ gul)
  decGU _ | no _ | no ¬p = no (contraposition guTl ¬p)

  newFrom : List B → Maybe GUList
  newFrom l with decGU l
  newFrom l | yes p = just (gulist l p)
  newFrom _ | no _ = nothing

  open GUList

  put : ∀ b l → List B
  put = _∷_

  put∈ : ∀ {x b l} → x ∈ l → x ∈ put b l
  put∈ = there

  putGUL : ∀ {b l} → f b ∉ l → GlobalUnicity l → GlobalUnicity (put b l)
  putGUL p _ (here refl) = here! refl p
  putGUL p = (λ {refl q → p q}) ∷ᵤ_

  put_into_when_ : ∀ b → (l : GUList) → f b ∉ (content l) → GUList
  put b into (gulist l gul) when p = gulist (put b l) (putGUL p gul)

  put_inside_ : B → GUList → Maybe GUList
  put b inside l with dec∉ (dec≡f dec) (f b) (content l)
  put b inside l | yes p = just (put b into l when p)
  put _ inside _ | no _ = nothing

  put_inside'_ : B → GUList → Maybe GUList
  put_inside'_ b = newFrom ∘ put b ∘ content

  assign_inside_when_ : ∀ b l (fb∈l : f b ∈ l) → List B
  assign b inside (_ ∷ l) when here _ = b ∷ l
  assign b inside (x ∷ l) when there fb∈l =
    x ∷ (assign b inside l when fb∈l)

  ∈assign : ∀ {a b l p} → a ∈ (assign b inside l when p) → a ∈ l
  ∈assign {p = here p} (here q) = here (trans q p)
  ∈assign {p = here _} (there q) = there q
  ∈assign {p = there _} (here q) = here q
  ∈assign {p = there _} (there q) = there (∈assign q)

  assign∈ : ∀ {a b l p} → a ∈ l → a ∈ (assign b inside l when p)
  assign∈ {p = here p} (here q) = here (trans q (sym p))
  assign∈ {p = here _} (there q) = there q
  assign∈ {p = there _} (here q) = here q
  assign∈ {p = there _} (there q) = there (assign∈ q)

  assign∈! : ∀ {a b l p} → a ∈! l → a ∈! (assign b inside l when p)
  assign∈! {p = here p} (here! x y) = here! (trans x (sym p)) y
  assign∈! {p = here p} (there! x y) = there! (x ∘ (flip trans) p) y
  assign∈! {p = there _} (here! x y) = here! x (contraposition ∈assign y)
  assign∈! {p = there _} (there! x y) = there! x (assign∈! y)

  ∈!assign : ∀ {a b l p} → a ∈! (assign b inside l when p) → a ∈! l 
  ∈!assign {p = here p} (here! x y) = here! (trans x p) y
  ∈!assign {p = here p} (there! x y) = there! (x ∘ (flip trans) (sym p)) y
  ∈!assign {p = there _} (here! x y) = here! x (contraposition assign∈ y)
  ∈!assign {p = there _} (there! x y) = there! x (∈!assign y)

  assignGUL : ∀ {b l p} → GlobalUnicity l
    → GlobalUnicity (assign b inside l when p)
  assignGUL gul = assign∈! ∘ gul ∘ ∈assign

  assign_inside_if_ : ∀ b l (fb∈l : f b ∈ content l) → GUList
  assign b inside gulist l gul if p = gulist
    (assign b inside l when p)
    (assignGUL gul)

  assign_inside_ : ∀ b (gul : GUList) → Maybe GUList
  assign b inside l with dec∈ (dec≡f dec) (f b) (content l)
  assign b inside l | yes p = just (assign b inside l if p)
  assign _ inside _ | no _ = nothing

  remove_from_when_ : ∀ a l (p : a ∈ l) → List B
  remove a from (b ∷ l) when here px = l
  remove a from (b ∷ l) when there a∈l = b ∷ remove a from l when a∈l

  ∉remove : ∀ {x a l p} → x ∉ l → x ∉ (remove a from l when p)
  ∉remove {p = here _} = contraposition there
  ∉remove {p = there _} x∉l (here px) = x∉l (here px)
  ∉remove {p = there p} x∉l (there x∈rm) =
    ∉remove {p = p} (contraposition there x∉l) x∈rm

  removeGUL : ∀ {a l p} → GlobalUnicity l
    → GlobalUnicity (remove a from l when p)
  removeGUL {p = here _} = guTl
  removeGUL {p = there _} gul =
    (λ x≡fb → ∉remove λ x∈xs →
      P→A→¬A! x≡fb x∈xs (gul (here x≡fb)))
        ∷ᵤ removeGUL (guTl gul)

  remove_from_ : ∀ a (gul : GUList) → Maybe GUList
  remove a from gulist l _ with dec∈ (dec≡f dec) a l
  remove a from gulist l gul | yes p =
    just (gulist (remove a from l when p) (removeGUL gul))
  remove _ from _ | no _ = nothing

  assignOrPut_inside_ : ∀ b (gul : GUList) → GUList
  assignOrPut b inside gulist l _ with dec∈ (dec≡f dec) (f b) l
  assignOrPut b inside gulist l gul | yes p =
    gulist (assign b inside l when p) (assignGUL gul)
  assignOrPut b inside gulist l gul | no ¬p =
    gulist (put b l) (putGUL ¬p gul)

  open RawMonad {f = a ⊔ b} monad

  collapse : ∀ {u} {X : Set u} → (X → GUList → Maybe GUList)
    → List X → GUList → Maybe GUList
  collapse g l gul = foldl (λ mgu → (mgu >>=_) ∘ g) (return gul) l

  putAll : List B → GUList → Maybe GUList
  putAll = collapse put_inside_

  removeAll : List A → GUList → Maybe GUList
  removeAll = collapse remove_from_

  assignAll : List B → GUList → Maybe GUList
  assignAll = collapse assign_inside_

  assignOrPutAll : List B → GUList → Maybe GUList
  assignOrPutAll = collapse λ x → just ∘ (assignOrPut x inside_)

  get_from_when_ : ∀ a l → a ∈ l → C
  get _ from (b ∷ _) when here _ = g b
  get a from (_ ∷ l) when there p = get a from l when p

  get_from_if_ : ∀ a l → a ∈ (content l) → C
  get a from l if p = get a from (content l) when p

  get_from_ : ∀ a l → Maybe C
  get a from l with dec∈ (dec≡f dec) a l
  get a from l | yes p = just (get a from l when p)
  get _ from _ | no ¬p = nothing

  get : ∀ a gul → Maybe C
  get a = get a from_ ∘ content

  _∈ₗ_ : REL A GUList _
  _∈ₗ_ x = x ∈_ ∘ content

  dec∈ₗ : Decidableᵣ _∈ₗ_
  dec∈ₗ x (gulist _ _) = dec∈ (dec≡f dec) x _

  contains : GUList → A → Bool
  contains gul x = does (dec∈ₗ x gul)

  private 
    elements : ∀ {x} {X : Set x} → (B → X) → GUList → List X
    elements f = (mapl f) ∘ content

  elementsF : GUList → List A
  elementsF = elements f

  elementsG : GUList → List C
  elementsG = elements g

  elementsId : GUList → List B
  elementsId = elements id

module Example1 where
  open Commands id Data.String._≟_ id
  open FunctionRelation {A = String} id
  open GlobalUnicity _≡f_
  open RawMonad {f = lzero} monad

  ex₁ : Maybe GUList
  ex₁ = return newGUL
    >>= putAll (⟦ "Judith" ↪ "Bob" ↪ "Alice" ⟧)

  ex₂ : Maybe GUList
  ex₂ = ex₁ >>= putAll (⟦ "Judith" ↪ "Hector" ⟧)

module Example2 where
  open Commands {B = ℕ × ℕ} (proj₁) (Data.Nat._≟_) (proj₂)
  open FunctionRelation {B = ℕ × ℕ} proj₁
  open GlobalUnicity _≡f_
  open RawMonad {f = lzero} monad

  ex₁ : Maybe GUList
  ex₁ = return newGUL
    >>= putAll (⟦ (3 , 4) ↪ (4 , 5) ↪ (5 , 5) ⟧)
    >>= assignOrPutAll (⟦ (4 , 7) ↪ (3 , 12) ↪ (3 , 10) ↪ (5 , 1) ⟧)

  ex₂ : Maybe GUList
  ex₂ = ex₁ >>= assignAll (⟦ (3 , 12) ↪ (4 , 10) ↪ (5 , 1) ⟧)

  ex₃ : Maybe GUList
  ex₃ = ex₂ >>= putAll (⟦ (12 , 4) ↪ (20 , 5) ↪ (3 , 12) ⟧)

  ex₄ : Maybe GUList
  ex₄ = ex₂ >>= assignAll (⟦ (3 , 6) ↪ (7 , 8) ↪ (5 , 1) ⟧)

  val₁ : Maybe ℕ
  val₁ = ex₄ >>= get 3

  val₂ : Maybe ℕ
  val₂ = ex₂ >>= get 3

  val₃ : Maybe ℕ
  val₃ = ex₂ >>= get 6

  el₁ : Maybe (List ℕ)
  el₁ = ex₂ >>= just ∘ elementsG

module ListInclusion {a ℓ} {A : Set a} {_≈_ : Rel A ℓ}
  (dec≈ : Decidableᵣ _≈_) (eq≈ : IsEquivalence _≈_) where
  open Membership _≈_

  _⊑_ : Rel (List A) _
  _⊑_ = _⊆_ on flip _∈_

  _≋_ : Rel (List A) _
  _≋_ = _⊑_ -[ _×_ ]- flip _⊑_

  open IsEquivalence renaming (trans to trans≈ ; refl to refl≈)

  conserv∈≈ : ∀ {x y l} → x ∈ l → y ≈ x → y ∈ l
  conserv∈≈  (here px) = here ∘ flip (trans≈ eq≈) px
  conserv∈≈  (there p) = there ∘ conserv∈≈ p

  dec⊑ : Decidableᵣ _⊑_
  dec⊑ []       l₂ = yes λ()
  dec⊑ (x ∷ l₁) l₂ with dec∈ dec≈ x l₂ | dec⊑ l₁ l₂
  dec⊑ _ _ | yes p | (yes p₁) =
    yes (λ {(here px) → conserv∈≈ p px ; (there x₂) → p₁ x₂})
  dec⊑ _ _ | yes _ | (no ¬p ) = no (λ x₁ → ¬p (λ x₃ → x₁ (there x₃)))
  dec⊑ _ _ | no ¬p | _        = no (λ x₁ → ¬p (x₁ (here (refl≈ eq≈))))

  dec≋ : Decidableᵣ _≋_
  dec≋ l₁ l₂ with dec⊑ l₁ l₂ | dec⊑ l₂ l₁
  dec≋ _ _ | yes p | (yes p₁) = yes (p , p₁)
  dec≋ _ _ | yes p | (no ¬p ) = no (¬p ∘ proj₂)
  dec≋ _ _ | no ¬p | _        = no (¬p ∘ proj₁)

  isEq≋ : IsEquivalence _≋_
  isEq≋ = record {
    refl = id , id ;
    sym = swap ;
    trans = zip (\f g → g ∘ f) \f g → f ∘ g }

module GUCompare {a b c} {A : Set a} {B : Set b} {C : Set c}
  (f     : B → A) (_≟a_ : Decidableᵣ {A = A} _≡_) (g     : B → C)
  (injfg : ∀ {x y} → (f x , g x) ≡ (f y , g y) → x ≡ y)
  (_≟b_ : Decidableᵣ {A = B} _≡_) where

  open Commands f _≟a_ g
  open ListInclusion _≟b_ isEquivalence
  open FunctionRelation f
  open Membership _≡f_ renaming (_∈_ to _∈f_ ; dec∈ to dec∈f)
  open Membership {A = B} _≡_
    renaming (_∈_ to _∈≡_ ; dec∈ to dec∈≡)
  open GlobalUnicity _≡f_
  open GUList

  dec∈fa : Decidableᵣ _
  dec∈fa = (dec∈f ∘ dec≡f) _≟a_

  _≋₁_ : Rel GUList _
  _≋₁_ = _≋_ on content

  eq≋₁ : IsEquivalence _≋₁_
  eq≋₁ with isEq≋
  eq≋₁ | record { refl = refl≋ ; sym = sym≋ ; trans = trans≋ }
    = record { refl = refl≋ ; sym = sym≋ ; trans = trans≋ }

  dec≋₁ : Decidableᵣ _≋₁_
  dec≋₁ (gulist l₁ _) (gulist l₂ _) = dec≋ l₁ l₂

  _≋₂_ : Rel GUList _
  gu₁ ≋₂ gu₂ = ∀ {x} → get x gu₁ ≡ get x gu₂

  eq≋₂ : IsEquivalence _≋₂_
  eq≋₂ = record
    { refl = refl ;
      sym = λ x → sym x ;
      trans = λ x x₁ → trans x x₁ }

  gu≡ : ∀ {b₀ b₁ l} → GlobalUnicity (b₀ ∷ l) → f b₁ ≡ f b₀
    → GlobalUnicity (b₁ ∷ l)
  gu≡ gulb₀ eq (here refl) =
    here! refl (contradiction (gulb₀ (here eq)) ∘ (P→A→¬A! eq))
  gu≡ gulb₀ eq (there q) =
    there! (λ p → ¬A!→P→¬A
      (gulb₀ (there q)) (trans p eq) q) (guTl gulb₀ q)

  ∈≡→∈f : ∀ {b b₁ l} → f b ≡ f b₁ → b ∈≡ l → (f b₁) ∈f l
  ∈≡→∈f px = mapAny λ {refl → sym px}

  ∈≡→∈f' : ∀ {b l} → b ∈≡ l → (f b) ∈f l
  ∈≡→∈f' = ∈≡→∈f refl

  get≡g : ∀ {b l p} → GlobalUnicity l → b ∈≡ l
    → get f b from l when p ≡ g b
  get≡g {p = here refl} _ (here refl) = refl
  get≡g {p = here px} gul (there b∈≡l) =
    contradiction (gul (here refl))
      (P→A→¬A! refl (∈≡→∈f px b∈≡l))
  get≡g {p = there p} gul (here refl) =
    contradiction (gul (here refl))
      (P→A→¬A! refl p)
  get≡g {p = there p} gul (there b∈≡l) = get≡g (guTl gul) b∈≡l

  g≡get : ∀ {b l p} → get f b from l when p ≡ g b → b ∈≡ l
  g≡get {p = here px} = here ∘ injfg ∘ (cong₂ _,_ px) ∘ sym
  g≡get {p = there p} = there ∘ g≡get

  get≡get : ∀ {b l l₁} → GlobalUnicity l
    → get f b from l ≡ get f b from l₁ → b ∈≡ l → b ∈≡ l₁
  get≡get {b} {l} _ _ with dec∈fa (f b) l
  get≡get {b} {l₁ = l₁} _ _ | yes _ with dec∈fa (f b) l₁
  get≡get gul eq | yes _ | yes _ =
    g≡get ∘ ((trans ∘ sym ∘ just-injective) eq) ∘ get≡g gul
  get≡get _ _ | no ¬p = ⊥-elim ∘ ¬p ∘ ∈≡→∈f'

  ≋₂→≋₁ : ∀ {gu₁ gu₂} → gu₁ ≋₂ gu₂ → gu₁ ≋₁ gu₂
  ≋₂→≋₁ {gu₁} {gu₂} gu₁≋₂gu₂ =
    let gu₂≋₂gu₁ = (IsEquivalence.sym eq≋₂) {gu₁} {gu₂} gu₁≋₂gu₂ in
    (get≡get (unique gu₁) gu₁≋₂gu₂) ,
    get≡get (unique gu₂) gu₂≋₂gu₁

  retrieve : ∀ {x l} → GlobalUnicity l → (p : x ∈f l)
    → ∃ λ y → y ∈≡ l × x ≡ f y × get x from l when p ≡ g y
  retrieve _ (here refl) = _ , here refl , refl , refl
  retrieve gul (there x∈fl) = map₂ (map₁ there) (retrieve (guTl gul) x∈fl)

  ≋₁→≋₂ : ∀ {gu₁ gu₂} → gu₁ ≋₁ gu₂ → gu₁ ≋₂ gu₂
  ≋₁→≋₂ {gulist l₁ _} {gulist l₂ _} _ {x} with dec∈fa x l₁ | dec∈fa x l₂
  ≋₁→≋₂ {gulist _ gul₁} {gulist _ gul₂} (l₁⊑l₂ , _) | yes p | yes _ =
    case retrieve gul₁ p of
      λ {(_ , q , refl , ≡get) →
        ((cong just) ∘ (trans ≡get) ∘ sym ∘ (get≡g gul₂) ∘ l₁⊑l₂) q}
  ≋₁→≋₂ {gulist _ gul₁} (l₁⊑l₂ , _)  | yes p | no ¬p =
    ⊥-elim (case retrieve gul₁ p of
      λ {(_ , q , refl , _) → (¬p ∘ ∈≡→∈f' ∘ l₁⊑l₂) q})
  ≋₁→≋₂ {_} {gulist _ gul₂} (_ , l₂⊑l₁) | no ¬p | yes p =
    ⊥-elim (case retrieve gul₂ p of
      λ {(_ , q , refl , _) → (¬p ∘ ∈≡→∈f' ∘ l₂⊑l₁) q})
  ≋₁→≋₂ _ | no _ | no _ = refl

  dec≋₂ : Decidableᵣ _≋₂_
  dec≋₂ gu₁ gu₂ with dec≋₁ gu₁ gu₂
  dec≋₂ gu₁ gu₂ | yes p = yes (≋₁→≋₂ {gu₁} {gu₂} p)
  dec≋₂ gu₁ gu₂ | no ¬p = no (¬p ∘ ≋₂→≋₁ {gu₁} {gu₂})
