open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (isPreorder) renaming (isEquivalence to isEquivalence≡ ; trans to trans≡)
open import Relation.Binary.Structures
open import Relation.Binary.Core
open import Relation.Binary.Lattice
open import Data.Sum renaming (swap to swap⊎)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary hiding (_⇒_)
open import Agda.Primitive
open import Function using (Fun₂)
open import Function.Base
open import Data.Empty
open import Function.Equality hiding (_∘_ ; const ; flip)
open import Function.Injection hiding (_∘_)
open import Function.Bijection hiding (_∘_)
open import Helper
open import Induction.WellFounded
open import Induction

module CCSL (Instant : StrictPartialOrder _ _ _) where

open import Interval Instant public

open IsPartialOrder using (isPreorder ; antisym)

Clock₀ : Set₁
Clock₀ = ∃ \Ticks → Trichotomous {A = ∃ Ticks} _≡'_ _≺'_

record Clock : Set₁ where
  constructor _⌞_ ; field
    Ticks : Pred Support _
    TTot : Trichotomous {A = ∃ Ticks} _≡'_ _≺'_

open Clock public

1⇒2 : Clock₀ → Clock
1⇒2 (Ticks , TTot) = Ticks ⌞ TTot

2⇒1 : Clock → Clock₀
2⇒1 (Ticks ⌞ TTot) = Ticks , TTot

≈→≡ : ∀ {c} {i j : ∃ (Ticks c)} → i ≈' j → i ≡' j
≈→≡ {c} {i} {j} with TTot c i j
≈→≡ | tri< a _ _ = ⊥-elim ∘ (≺→¬≈ (inj₁ a))
≈→≡ | tri≈ _ b _ = const b
≈→≡ | tri> _ _ c = ⊥-elim ∘ (≺→¬≈ (inj₂ c))

passive : Pred Clock _
passive = Empty ∘ Ticks

active : Pred Clock _
active = ¬_ ∘ passive

_filterBy_ : Clock → (Pred _ _) → Clock 
((Ticks ⌞ _) filterBy P) .Ticks = Ticks ∩ P
((_ ⌞ TTot) filterBy _) .TTot (x , y , _) (x₁ , y₁ , _)
  = TTot (x , y) (x₁ , y₁)

_filterBy'_ : Clock → (Pred _ _) → Clock
(Ticks ⌞ TTot) filterBy' P
  = (Ticks ∩ P) ⌞ λ {(x , y , _) (x₁ , y₁ , _) → TTot (x , y) (x₁ , y₁)}

passiveFilter : ∀ {c P} → passive c → passive (c filterBy P)
passiveFilter p x = p x ∘ proj₁

activeFilter : ∀ {c P} → active (c filterBy P) → active c
activeFilter {c} = _∘ (passiveFilter {c})

_∣ᵢ_ : Clock → Interval → Clock
c ∣ᵢ I  = c filterBy (_∈ᵢ I)

_ticksIn_ : Clock → Interval → Set
c ticksIn I = active (c ∣ᵢ I)

_iddlesIn_ : Clock → Interval → Set
c iddlesIn I = passive (c ∣ᵢ I)

presIddles : ∀ {c I₀ I₁} → c iddlesIn I₁ → I₀ ⊂ᵢ I₁ → c iddlesIn I₀
presIddles passcI₁ I₀⊂ᵢI₁ i (ti , i∈I₀) = passcI₁ i (ti , I₀⊂ᵢI₁ i∈I₀)

presTicks : ∀ {c I₀ I₁} → c ticksIn I₀ → I₀ ⊂ᵢ I₁ → c ticksIn I₁
presTicks {c} p I₀⊂ᵢI₁ passcI₁ = p (presIddles {c} passcI₁ I₀⊂ᵢI₁)

_diesIn_ : REL Clock Interval _
c diesIn I = ∃ λ i → i ∈ᵢ I × Ticks c i × (∀ j → Ticks c j → i ≼ j → j ∈ᵢ I) 

_diesOn_ : REL Clock Support _
c diesOn i = c diesIn ⟦ i - i ⟧

dies≈ : ∀ {i j c} → c diesOn i → c diesOn j → i ≈ j
dies≈ {c = c} (_ , o∈ii , tco , _) (_ , u∈jj , tcu , _)
  with sameB refl≈ o∈ii | sameB refl≈ u∈jj | TTot c (_ , tco) (_ , tcu)
dies≈ _ _ | o≈i | u≈j | tri≈ _ refl _ =
  trans≈ (sym≈ o≈i) (trans≈ refl≈ u≈j)
dies≈ (_ , _ , _ , po) (u , _ , tcu , _) | o≈i | _ | tri< o≺u _ _ =
  contradiction
    (sym≈ (trans≈ (sameB refl≈ (po u tcu (inj₂ o≺u))) (sym≈ o≈i)))
    (≺→¬≈ (inj₁ o≺u))
dies≈ (o , _ , tco , _) (_ , _ , _ , pu) | _ | u≈j | tri> _ _ u≺o = 
  contradiction
    (trans≈ (sameB refl≈ (pu o tco (inj₂ u≺o))) (sym≈ u≈j))
    (≺→¬≈ (inj₂ u≺o))

staysDead : ∀ {i d c} → c diesOn d → d ≺ i → c iddlesIn ⟦ i -∞⟦
staysDead (_ , d∈xx , _ , p) d≺i j (tcj , i≼j) = proj₂
  (p j tcj (trans≼ (≼-resp-≈₂
  (sym≈ (sameB refl≈ d∈xx)) (inj₂ d≺i)) i≼j)) (trans≺≼ d≺i i≼j)

CCSLRelation : Set₁
CCSLRelation = Rel Clock _

CCSLRelationᵢ : Set₁
CCSLRelationᵢ = Interval → CCSLRelation

toRelᵢ : CCSLRelation → CCSLRelationᵢ
toRelᵢ _CR_ I = _CR_ on (_filterBy (_∈ᵢ I))

toRelᵢWithP : CCSLRelation → CCSLRelationᵢ → CCSLRelationᵢ
toRelᵢWithP _CR_ CRᵢ I c₁ c₂ = toRelᵢ _CR_ I c₁ c₂ × CRᵢ I c₁ c₂

_⊑_ : CCSLRelation
(Tc₁ ⌞ _) ⊑ (Tc₂ ⌞ _) = ∀ (x₁ : ∃ Tc₁) → ∃ \(x₂ : ∃ Tc₂) → x₁ ≈' x₂

trans⊑ : Transitive _⊑_
trans⊑ c₁⊑c₂ _    x with c₁⊑c₂ x
trans⊑ _    c₂⊑c₃ _ | y , _   with c₂⊑c₃ y
trans⊑ _    _    _ | _ , x≈y | z , y≈z = z , trans≈ x≈y y≈z

refl⊑ : Reflexive _⊑_
refl⊑ = _, refl≈

isPreorder≡⊑ : IsPreorder _≡_ _⊑_
isPreorder≡⊑ = record {
  isEquivalence = isEquivalence≡ ;
  reflexive = λ { {c} refl → refl⊑ {c}} ;
  trans = λ {c₁} {c₂} {c₃} → trans⊑ {c₁} {c₂} {c₃}}

opToRel : ∀ {c P} → (c filterBy P) ⊑ c
opToRel (i , tci , _) = (i , tci) , refl≈

_∽_ : CCSLRelation
c₁ ∽ c₂ = c₁ ⊑ c₂ × c₂ ⊑ c₁

isEq∽ : IsEquivalence _∽_
isEq∽ .IsEquivalence.refl = (_, refl≈) , _, refl≈
isEq∽ .IsEquivalence.sym = swap
isEq∽ .IsEquivalence.trans {i} {j} {k} (i⊑j , j⊑i) (j⊑k , k⊑j) =
  trans⊑ {i} {j} {k} i⊑j j⊑k , trans⊑ {k} {j} {i} k⊑j j⊑i

isPartialOrder∽⊑ : IsPartialOrder _∽_ _⊑_
isPartialOrder∽⊑ .isPreorder .IsPreorder.isEquivalence = isEq∽
isPartialOrder∽⊑ .isPreorder .IsPreorder.reflexive = proj₁
isPartialOrder∽⊑ .isPreorder .IsPreorder.trans {c₁} {c₂} {c₃} =
  trans⊑ {c₁} {c₂} {c₃}
isPartialOrder∽⊑ .antisym = _,_

relToOp : ∀ {c₀ c₁} → c₀ ⊑ c₁ → ∃ (_∽ c₀ ∘ c₁ filterBy_)

relToOp {c₀} {c₁} c₀⊑c₁ =
  (λ i → ∃ \j → Ticks c₀ j × i ≈ j) ,
  (λ {(_ , _ , j , tc₀j , i≈j) → (j , tc₀j) , i≈j}) ,
  λ {(i , tc₀i) → case c₀⊑c₁ (i , tc₀i) of
    λ {((j , tc₁j) , i≈j) → (j , tc₁j , i , tc₀i , sym≈ i≈j) , i≈j}}

_♯_ : CCSLRelation
(Tc₁ ⌞ _) ♯ (Tc₂ ⌞ _) = ∀ (x : ∃ Tc₁) (y : ∃ Tc₂) → ¬ x ≈' y

sym♯ : Symmetric _♯_
sym♯ p x y = (p y x) ∘ sym≈

♯⊑ : ∀ {c₁ c₂ c₃ c₄} → c₂ ♯ c₄ → c₁ ⊑ c₂ → c₃ ⊑ c₄ → c₁ ♯ c₃
♯⊑ c₂♯c₄ c₁⊑c₂ c₃⊑c₄ i j i≈'j with c₁⊑c₂ i | c₃⊑c₄ j
♯⊑ c₂♯c₄ _ _ _ _ i≈j | k , i≈k | l , j≈l =
  c₂♯c₄ k l (trans≈ (sym≈ i≈k) (trans≈ i≈j j≈l))

♯×⊑→⊥ : ∀ {c₁ c₂} → c₁ ♯ c₂ → c₁ ⊑ c₂ → passive c₁
♯×⊑→⊥ c₁♯c₂ c₁⊑c₂ i tc₁i with c₁⊑c₂ (i , tc₁i)
♯×⊑→⊥ c₁♯c₂ c₁⊑c₂ i tc₁i | j , i≈j = c₁♯c₂ (i , tc₁i) j i≈j

record Precedence (_<_ : Rel Support _) (c₁ c₂ : Clock) : Set where
  field
    h : ∃ (Ticks c₂) → ∃ (Ticks c₁)
    congruent : ∀ {i j} → i ≈' j → h i ≈' h j
    precedes : ∀ i → proj₁ (h i) < proj₁ i
    preserves : ∀ {i j} → i ≺' j → h i ≺' h j
    dense : ∀ {i j} {p : ∃ (Ticks c₁)} →
      h i ≺' p → p ≺' h j → ∃ (_≈' p ∘ h)

  preserves← : ∀ {i j} → h i ≺' h j → i ≺' j
  preserves← {i} {j} with TTot c₂ i j
  preserves← | tri< a _ _ = const a
  preserves← | tri≈ _ b _ = ⊥-elim ∘ (irrefl≈≺ ∘ congruent) (≡→≈ b)
  preserves← | tri> _ _ c = ⊥-elim ∘ (≼→¬≺ ∘ inj₂ ∘ preserves) c

  h′ : (_⟶_ on (toSetoid ∘ Ticks)) c₂ c₁
  h′ = record { _⟨$⟩_ = h ; cong = congruent}

  injective : Injective h′
  injective {i} {j} with TTot c₂ i j
  injective | tri< a _ _ = (contradiction a) ∘
    (contraposition preserves) ∘ ≼→¬≺ ∘ inj₁ ∘ sym≈
  injective | tri≈ _ b _ = const (≡→≈ b)
  injective | tri> _ _ c = (contradiction c) ∘
    (contraposition preserves) ∘ ≼→¬≺ ∘ inj₁

  bijective : Bijective (imageFunction h′)
  bijective = injtobij injective

_≺≺_ : CCSLRelation
_≺≺_ = Precedence _≺_

_≼≼_ : CCSLRelation
_≼≼_ = Precedence _≼_

open Precedence public

tprec : ∀ {R} → Transitive R → (Transitive ∘ Precedence) R
tprec _ p₁₂ p₂₃ .h = (h p₁₂) ∘ (h p₂₃)
tprec _ p₁₂ p₂₃ .congruent = (congruent p₁₂) ∘ (congruent p₂₃)
tprec tr p₁₂ p₂₃ .precedes = (tr (precedes p₁₂ _)) ∘ (precedes p₂₃)
tprec _ p₁₂ p₂₃ .preserves = (preserves p₁₂) ∘ (preserves p₂₃)
tprec _ p₁₂ p₂₃ .dense {p = k} ≺k k≺ with dense p₁₂ {p = k} ≺k k≺
tprec _ p₁₂ p₂₃ .dense ≺k k≺ | l , hl≈p with dense p₂₃ {p = l}
  (preserves← p₁₂ (≺-resp-≈₁ (sym≈ hl≈p) ≺k))
  (preserves← p₁₂ (≺-resp-≈₂ (sym≈ hl≈p) k≺))
tprec _ p₁₂ p₂₃ .dense _ _  | m , hm≈p | n , hn≈p =
  n , trans≈ (congruent p₁₂ hn≈p) hm≈p

trans≺≺ : Transitive _≺≺_
trans≺≺ = tprec trans≺

trans≼≼ : Transitive _≼≼_
trans≼≼ = tprec trans≼

≺≺-respʳ-∽ : _≺≺_ Respectsʳ _∽_
≺≺-respˡ-∽ : _≺≺_ Respectsˡ _∽_

≺≺-respʳ-∽ (_ , c₃⊑c₂) c₁≺≺c₂ .h = (h c₁≺≺c₂) ∘ proj₁ ∘ c₃⊑c₂
≺≺-respʳ-∽ {_} {c₂} (_ , c₃⊑c₂) c₁≺≺c₂ .congruent =
  (congruent c₁≺≺c₂) ∘
  (trans≈ ((sym≈ ∘ proj₂ ∘ c₃⊑c₂) _)) ∘
  (flip trans≈ ((proj₂ ∘ c₃⊑c₂) _))
≺≺-respʳ-∽ (_ , c₃⊑c₂) c₁≺≺c₂ .precedes =
  (flip ≺-resp-≈₁ (precedes c₁≺≺c₂ _)) ∘ sym≈ ∘ proj₂ ∘ c₃⊑c₂
≺≺-respʳ-∽ (_ , c₃⊑c₂) c₁≺≺c₂ .preserves =
  (preserves c₁≺≺c₂) ∘
  (≺-resp-≈₂ ((proj₂ ∘ c₃⊑c₂) _)) ∘
  (≺-resp-≈₁ ((proj₂ ∘ c₃⊑c₂) _))
≺≺-respʳ-∽ {_} {c₂} (c₂⊑c₃ , c₃⊑c₂) c₁≺≺c₂ .dense {p = p} u v =
  ((proj₁ ∘ c₂⊑c₃ ∘ proj₁ ∘ (dense c₁≺≺c₂ {p = p} u)) v) ,
  trans≈ (congruent c₁≺≺c₂ ((sym≈ (trans≈ ((proj₂ ∘ c₂⊑c₃) _)
  ((proj₂ ∘ c₃⊑c₂ ∘ proj₁ ∘ c₂⊑c₃) _)))))
  (proj₂ (dense c₁≺≺c₂ u v))

≺≺-respˡ-∽ (c₂⊑c₃ , _) c₂≺≺c₁ .h =
  proj₁ ∘ c₂⊑c₃ ∘ h c₂≺≺c₁
≺≺-respˡ-∽ {_} {_} {c₃} (c₂⊑c₃ , _) c₂≺≺c₁ .congruent =
  (flip trans≈ ((proj₂ ∘ c₂⊑c₃) _)) ∘
  (trans≈ ((sym≈ ∘ proj₂ ∘ c₂⊑c₃) _)) ∘
  (congruent c₂≺≺c₁)
≺≺-respˡ-∽ (c₂⊑c₃ , _) c₂≺≺c₁ .precedes =
  (≺-resp-≈₂ ((proj₂ ∘ c₂⊑c₃) _)) ∘
  (precedes c₂≺≺c₁) 
≺≺-respˡ-∽ (c₂⊑c₃ , _) c₂≺≺c₁ .preserves =
  ≺-resp-≈₁ ((proj₂ ∘ c₂⊑c₃) _) ∘
  ≺-resp-≈₂ ((proj₂ ∘ c₂⊑c₃) _) ∘
  preserves c₂≺≺c₁
≺≺-respˡ-∽ {c₁} {c₂} {c₃} (c₂⊑c₃ , c₃⊑c₂) c₂≺≺c₁ .dense {p = p} u v
  with c₃⊑c₂ p
≺≺-respˡ-∽ {c₁} {c₂} {c₃} (c₂⊑c₃ , c₃⊑c₂) c₂≺≺c₁ .dense {p = p} u v |
  q , p≈q with dense c₂≺≺c₁ {p = q} (≺-resp-≈₁ p≈q (≺-resp-≈₂
  ((sym≈ ∘ proj₂ ∘ c₂⊑c₃ ∘ h c₂≺≺c₁) _) u))
  (≺-resp-≈₁ ((sym≈ ∘ proj₂ ∘ c₂⊑c₃ ∘ h c₂≺≺c₁) _)
  (≺-resp-≈₂ p≈q v))
≺≺-respˡ-∽ {c₁} {c₂} {c₃} (c₂⊑c₃ , c₃⊑c₂) c₂≺≺c₁ .dense {p = p} _ _
  | q , p≈q | r , hr≈q = r , 
  (trans≈ ((sym≈ ∘ proj₂ ∘ c₂⊑c₃ ∘ h c₂≺≺c₁) r)
  (trans≈ hr≈q (sym≈ p≈q)))

c≺≺∅ : ∀ {c e} → passive e → c ≺≺ e
c≺≺∅ p = record
  { h = λ {(i , ti) → ⊥-elim (p i ti)}
  ; congruent = λ { {i , ti} _ → ⊥-elim (p i ti)}
  ; precedes = λ {(i , ti) → ⊥-elim (p i ti)}
  ; preserves = λ { {i , ti} _ → ⊥-elim (p i ti)}
  ; dense = λ { {i , ti} _ → ⊥-elim (p i ti)}}

∅≺≺∅ : ∀ {e} → passive e → e ≺≺ e
∅≺≺∅ = c≺≺∅

record InitialClock : Set₁ where
  field
    clock : Clock
    first : ∃ λ (x : ∃ (Ticks clock)) → ∀ (y : ∃ (Ticks clock)) → x ≼' y

open InitialClock

_∽ᵢ_ : Rel InitialClock _
_∽ᵢ_ = _∽_ on clock

_≺≺ᵢ_ : Rel InitialClock _
_≺≺ᵢ_ = _≺≺_ on clock

≺≺-irrefl : Irreflexive _∽ᵢ_ _≺≺ᵢ_
≺≺-irrefl {y = c₂} _ _ with first c₂
≺≺-irrefl c₁∽c₂ c₁≺≺c₂ | f , f≼x with proj₁ c₁∽c₂ (h c₁≺≺c₂ f)
≺≺-irrefl _ c₁≺≺c₂ | f , f≼x | g , hf≈g =
  irrefl≈≺ hf≈g (trans≺≼ (precedes c₁≺≺c₂ f) (f≼x g))

open IsStrictPartialOrder

≺≺-ispo : IsStrictPartialOrder _∽ᵢ_ _≺≺ᵢ_
≺≺-ispo .isEquivalence =
  record { refl = (_, refl≈) , _, refl≈ ; sym = swap ;
    trans = λ { {record {clock = i}}
      {record {clock = j}} {record {clock = k}}
      (i⊑j , j⊑i) (j⊑k , k⊑j) → trans⊑ {i} {j} {k} i⊑j j⊑k
      , trans⊑ {k} {j} {i} k⊑j j⊑i} }
≺≺-ispo .irrefl {i} {j} = ≺≺-irrefl {i} {j}
≺≺-ispo .trans = trans≺≺
≺≺-ispo .<-resp-≈ = ≺≺-respʳ-∽ , ≺≺-respˡ-∽

refl≼≼ : _∽_ ⇒ _≼≼_
refl≼≼ {c₁} (c₁⊑c₂ , c₂⊑c₁) = record {
  h = proj₁ ∘ c₂⊑c₁ ;
  congruent = 
    flip trans≈ (proj₂ (c₂⊑c₁ _)) ∘
    (trans≈ ((sym≈ ∘ proj₂ ∘ c₂⊑c₁) _)) ;
  precedes = inj₁ ∘ sym≈ ∘ proj₂ ∘ c₂⊑c₁ ;
  preserves = ≺-resp-≈₂ ((proj₂ ∘ c₂⊑c₁) _) ∘
    (≺-resp-≈₁ ((proj₂ ∘ c₂⊑c₁) _)) ;
  dense = λ {_} {_} {p} _ _ → proj₁ (c₁⊑c₂ p) ,
    (trans≈ (sym≈
    ((proj₂ ∘ c₂⊑c₁ ∘ proj₁ ∘ c₁⊑c₂) p))
    ((sym≈ ∘ proj₂ ∘ c₁⊑c₂) p))}

isPreorder≡≼≼ : IsPreorder _∽_ _≼≼_
isPreorder≡≼≼ = record {
  isEquivalence = isEq∽ ; reflexive = refl≼≼ ; trans = trans≼≼ }

record WFClock : Set₁ where
  field clock : Clock ; wf-≺ : WellFounded (_≺'_ {P = Ticks clock})

open WFClock

_∽ₒ_ : Rel WFClock _
_∽ₒ_ = _∽_ on clock

_≼≼ₒ_ : Rel WFClock _
_≼≼ₒ_ = _≼≼_ on clock

i≈hi : ∀ {c₁ c₂} (₁≼₂ : c₁ ≼≼ₒ c₂) (₂≼₁ : c₂ ≼≼ₒ c₁) i →
  i ≈' ((h ₁≼₂) ∘ (h ₂≼₁)) i → i ≈' h ₂≼₁ i
i≈hi ₁≼₂ ₂≼₁ i p with precedes ₂≼₁ i
i≈hi ₁≼₂ ₂≼₁ i p | inj₁ x = sym≈ x
i≈hi {c₁} {c₂} ₁≼₂ ₂≼₁ i p | inj₂ y =
  ⊥-elim ((≺→¬≈ (inj₂ (trans≼≺ (precedes ₁≼₂ (h ₂≼₁ i)) y))) p)

auxi≈h₁hi : ∀ {c₁ c₂} (₁≼₂ : c₁ ≼≼ₒ c₂) (₂≼₁ : c₂ ≼≼ₒ c₁) i →
  ({x : ∃ (Ticks (clock c₁))} → x ≺' i → x ≈' (h ₁≼₂ (h ₂≼₁ x))) →
  (h ₁≼₂ (h ₂≼₁ i)) ≺' i → i ≈' (h ₁≼₂ (h ₂≼₁ i))
auxi≈h₁hi {c₁} {c₂} ₁≼₂ ₂≼₁ i p h₁hi≺i = let h , h₁ = h ₂≼₁ , h ₁≼₂ in
  let h₁hi≈h₁hh₁hi = p {(h₁ ∘ h) i} h₁hi≺i in
  let h₁hi≈hh₁hi = i≈hi {c₁} {c₂} ₁≼₂ ₂≼₁ ((h₁ ∘ h) i) h₁hi≈h₁hh₁hi in
  let hh₁hi≺hi = preserves ₂≼₁ {(h₁ ∘ h) i} {i} h₁hi≺i in
  let h₁hh₁hi≺h₁hi = preserves ₁≼₂ {(h ∘ h₁ ∘ h) i} {h i} hh₁hi≺hi in
    ⊥-elim (≼→¬≺ (inj₁ h₁hi≈h₁hh₁hi) h₁hh₁hi≺h₁hi)

step : ∀ {c₁ c₂} (₁≼₂ : c₁ ≼≼ₒ c₂) (₂≼₁ : c₂ ≼≼ₒ c₁) i → (∀ {x} →
  x ≺' i → x ≈' ((h ₁≼₂) ∘ (h ₂≼₁)) x) → i ≈' ((h ₁≼₂) ∘ (h ₂≼₁)) i
step ₁≼₂ ₂≼₁ i p with precedes ₂≼₁ i | precedes ₁≼₂ (h ₂≼₁ i)
step ₁≼₂ ₂≼₁ i p | inj₁ x | inj₁ y = sym≈ (trans≈ y x)
step {c₁} {c₂} ₁≼₂ ₂≼₁ i p | inj₁ hi≈i | inj₂ h₁hi≺hi =
  auxi≈h₁hi {c₁} {c₂} ₁≼₂ ₂≼₁ i p (trans≺≼ h₁hi≺hi (inj₁ hi≈i))
step {c₁} {c₂} ₁≼₂ ₂≼₁ i p | inj₂ hi≺i | inj₁ h₁hi≈hi =
  auxi≈h₁hi {c₁} {c₂} ₁≼₂ ₂≼₁ i p (trans≼≺ (inj₁ h₁hi≈hi) hi≺i)
step {c₁} {c₂} ₁≼₂ ₂≼₁ i p | inj₂ hi≺i | inj₂ h₁hi≺hi =
  auxi≈h₁hi {c₁} {c₂} ₁≼₂ ₂≼₁ i p (trans≺ h₁hi≺hi hi≺i)

i≈h₁∘hi : ∀ {c₁ c₂} (₁≼₂ : c₁ ≼≼ₒ c₂) (₂≼₁ : c₂ ≼≼ₒ c₁) i →
  i ≈' ((h ₁≼₂) ∘ (h ₂≼₁)) i
i≈h₁∘hi {c₁} {c₂} ₁≼₂ ₂≼₁ i = let open All (wf-≺ c₁) in
  wfRec _ (λ j → j ≈' ((h ₁≼₂) ∘ (h ₂≼₁)) j)
  (λ i ri → step {c₁} {c₂} ₁≼₂ ₂≼₁ i (ri _)) i

≼≼-antisym-∽ : Antisymmetric _∽ₒ_ _≼≼ₒ_
≼≼-antisym-∽ {c₁} {c₂} ₁≼₂ ₂≼₁ =
  (λ i → h ₂≼₁ i , i≈hi {c₁} {c₂} ₁≼₂ ₂≼₁ i (i≈h₁∘hi {c₁} {c₂} ₁≼₂ ₂≼₁ i)) ,
  λ i → h ₁≼₂ i , i≈hi {c₂} {c₁} ₂≼₁ ₁≼₂ i (i≈h₁∘hi {c₂} {c₁} ₂≼₁ ₁≼₂ i)

≼≼-ipo : IsPartialOrder _∽ₒ_ _≼≼ₒ_
≼≼-ipo = record {
  isPreorder = record {
    isEquivalence = record {
      refl = (_, refl≈) , _, refl≈ ;
      sym = swap ;
      trans =  λ { {record {clock = i}} {record {clock = j}}
        {record {clock = k}} (i⊑j , j⊑i) (j⊑k , k⊑j) →
        trans⊑ {i} {j} {k} i⊑j j⊑k , trans⊑ {k} {j} {i} k⊑j j⊑i} } ;
    reflexive = refl≼≼ ;
    trans = trans≼≼ } ;
  antisym = λ {i} {j} → ≼≼-antisym-∽ {i} {j} }

record _≪≫_ (c₁ c₂ : Clock) : Set where
  field
    precedence : c₁ ≺≺ c₂
    alternate : ∀ {i j : ∃ (Ticks c₂)} → i ≺' j → i ≺' h precedence j

CCSLExpression : ∀ {a} → Set _
CCSLExpression {a} = Clock → Clock → Clock → Set a

_≋_⋂_ : CCSLExpression
(Tc ⌞ _) ≋ Tc₁ ⌞ _ ⋂ (Tc₂ ⌞ _) =
  (∀ (x : ∃ Tc) → ∃ λ (y : ∃ Tc₁) → ∃ λ (z : ∃ Tc₂) → x ≈' y × x ≈' z) ×
  (∀ (y : ∃ Tc₁) (z : ∃ Tc₂) → y ≈' z → ∃ λ (x : ∃ Tc) → x ≈' y)

passc≋c₁♯c₂ : ∀ {c c₁ c₂} → c ≋ c₁ ⋂ c₂ → c₁ ♯ c₂ → passive c
passc≋c₁♯c₂ (c→c₁c₂ , _) c₁♯c₂ i tci =
  let (y , z , x≈y , x≈z) = c→c₁c₂ (i , tci) in
    c₁♯c₂ y z (trans≈ (sym≈ x≈y) x≈z)

symInter : ∀ {c} → Symmetric (c ≋_⋂_)
symInter (c→c₁c₂ , c₁c₂→c) =
  (λ x → case c→c₁c₂ x of λ {(y , z , x≈y , y≈z) → z , y , y≈z , x≈y}) ,
  (λ y z x → case (c₁c₂→c z y) (sym≈ x) of
    λ {(t , t≈z) → t , trans≈ t≈z (sym≈ x)})

subInterₗ : ∀ {c c₁ c₂} → c ≋ c₁ ⋂ c₂ → c ⊑ c₁
subInterₗ (c→c₁c₂ , _) x with c→c₁c₂ x
subInterₗ (_     , _) _ | y , _ , x≈y , _ = y , x≈y

subInterᵣ : ∀ {c c₁ c₂} → c ≋ c₁ ⋂ c₂ → c ⊑ c₂
subInterᵣ {c} {c₁} {c₂} =
  subInterₗ {c} {c₂} {c₁} ∘ symInter {c} {c₁} {c₂}

≋⋂→⊑ : ∀ {c₀ c c₁ c₂} → c₀ ≋ c₁ ⋂ c₂ → c ≋ c₁ ⋂ c₂ → c ⊑ c₀
≋⋂→⊑ (_ , c₁c₂→c₀) (c→c₁c₂ , _) x =
  let y , z , x≈y , x≈z = c→c₁c₂ x in
  let t , t≈y = c₁c₂→c₀ y z (trans≈ (sym≈ x≈y) x≈z) in
  t , trans≈ x≈y (sym≈ t≈y)

unicityInter : ∀ {c₀ c c₁ c₂} → c₀ ≋ c₁ ⋂ c₂ → c ≋ c₁ ⋂ c₂ → c ∽ c₀
unicityInter {c₀} {c} {c₁} {c₂} p q =
  ≋⋂→⊑ {c₀} {c} {c₁} {c₂} p q , ≋⋂→⊑ {c} {c₀} {c₁} {c₂} q p

⊑→≋⋂ : ∀ {c₁ c₂} → c₁ ⊑ c₂ → c₁ ≋ c₁ ⋂ c₂
⊑→≋⋂ c₁⊑c₂ =
  (λ x → x , let (y , x≈y) = c₁⊑c₂ x in y , refl≈ , x≈y) , λ x _ _ → x , refl≈

⊑⊑→⊑⋂ : ∀ {c₀ c c₁ c₂} → c₀ ⊑ c₁ → c₀ ⊑ c₂ → c ≋ c₁ ⋂ c₂ → c₀ ⊑ c
⊑⊑→⊑⋂ c₀⊑c₁ c₀⊑c₂ (_ , c₁c₂→c) x₀ =
  let (x₁ , x₀≈x₁) = c₀⊑c₁ x₀ in
  let (x₂ , x₀≈x₂) = c₀⊑c₂ x₀ in
  let (x , p) = c₁c₂→c x₁ x₂ (trans≈ (sym≈ x₀≈x₁) x₀≈x₂) in
    x , trans≈ x₀≈x₁ (sym≈ p)

_≋_⋃_ : CCSLExpression
(Tc ⌞ _) ≋ (Tc₁ ⌞ _) ⋃ (Tc₂ ⌞ _) =
  (∀ (y : ∃ Tc) → ∃ λ (x : ∃ (Tc₁ ∪ Tc₂)) → x ≈' y) ×
  (∀ (x : ∃ (Tc₁ ∪ Tc₂)) → ∃ λ (y : ∃ Tc) → x ≈' y)

symUnion : ∀ {c} → Symmetric (c ≋_⋃_)
symUnion (c→c₁c₂ , c₁c₂→c) =
  (λ x → let ((y , ty) , p) = c→c₁c₂ x
    in (y , swap⊎ ty) , p) ,
       λ {(x , tx) → c₁c₂→c (x , swap⊎ tx)}

subUnionₗ : ∀ {c c₁ c₂} → c ≋ c₁ ⋃ c₂ → c₁ ⊑ c
subUnionₗ (_ , c₁c₂→c) (x , Tc₁x) = c₁c₂→c (x , inj₁ Tc₁x)

subUnionᵣ : ∀ {c c₁ c₂} → c ≋ c₁ ⋃ c₂ → c₂ ⊑ c
subUnionᵣ {c} {c₁} {c₂} =
  subUnionₗ {c} {c₂} {c₁} ∘ symUnion {c} {c₁} {c₂}

≋⋃→⊑ : ∀ {c₀ c c₁ c₂} → c₀ ≋ c₁ ⋃ c₂ → c ≋ c₁ ⋃ c₂ → c ⊑ c₀
≋⋃→⊑ (_ , c₁c₂→c₀) (c→c₁c₂ , _) x = let (y , x≈y) = c→c₁c₂ x in
  let z , y≈z = c₁c₂→c₀ y in z , trans≈ (sym≈ x≈y) y≈z

unicityUnion : ∀ {c₀ c c₁ c₂} → c₀ ≋ c₁ ⋃ c₂ → c ≋ c₁ ⋃ c₂ → c ∽ c₀
unicityUnion {c₀} {c} {c₁} {c₂} p q =
  ≋⋃→⊑ {c₀} {c} {c₁} {c₂} p q , ≋⋃→⊑ {c} {c₀} {c₁} {c₂} q p

⊑→≋⋃ : ∀ {c₁ c₂} → c₁ ⊑ c₂ → c₂ ≋ c₁ ⋃ c₂
⊑→≋⋃ c₁⊑c₂ =
  (λ {(x , tc₁x) → (x , inj₂ tc₁x) , refl≈}) ,
  λ {(x , inj₁ tcx) → c₁⊑c₂ (x , tcx) ; (x , inj₂ tc₁x) → (x , tc₁x) , refl≈}

⊑⊑→⊑⋃ : ∀ {c₀ c c₁ c₂} → c₁ ⊑ c₀ → c₂ ⊑ c₀ → c ≋ c₁ ⋃ c₂ → c ⊑ c₀
⊑⊑→⊑⋃ c₁⊑c₀ c₂⊑c₀ (c→c₁c₂ , _) x with c→c₁c₂ x
⊑⊑→⊑⋃ c₁⊑c₀ c₂⊑c₀ (c→c₁c₂ , _) x | (x₁ , inj₁ tx₁) , x₁≈x =
  let (x₀ , x₁≈x₀) = c₁⊑c₀ (x₁ , tx₁) in x₀ , trans≈ (sym≈ x₁≈x) x₁≈x₀
⊑⊑→⊑⋃ c₁⊑c₀ c₂⊑c₀ (c→c₁c₂ , _) x | (x₂ , inj₂ tx₂) , x₂≈x =
  let (x₀ , x₂≈x₀) = c₂⊑c₀ (x₂ , tx₂) in x₀ , trans≈ (sym≈ x₂≈x) x₂≈x₀

record SpecLattice⋃⋂ (_∧_ _∨_ : Clock → Clock → Clock) : Set₁ where
  field
    inter∧ : ∀ {c₁ c₂} → (c₁ ∧ c₂) ≋ c₁ ⋂ c₂
    union∨ : ∀ {c₁ c₂} → (c₁ ∨ c₂) ≋ c₂ ⋃ c₁

specToLattice⋃⋂ : ∀ {_∧_ _∨_}
  → SpecLattice⋃⋂ _∧_ _∨_ → IsLattice _∽_ _⊑_ _∨_ _∧_

specToLattice⋃⋂ {_∧_} {_∨_}
  record { inter∧ = inter∧ ; union∨ = union∨ } =
  record {
    isPartialOrder = isPartialOrder∽⊑ ;
    supremum = λ c₁ c₂ →
      subUnionᵣ {c₁ ∨ c₂} {c₂} {c₁} union∨ ,
      subUnionₗ {c₁ ∨ c₂} {c₂} {c₁} union∨ ,
      λ c₀ c₁⊑c₀ c₂⊑c₀ →
        ⊑⊑→⊑⋃ {c₀} {c₁ ∨ c₂} {c₂} {c₁} c₂⊑c₀ c₁⊑c₀ union∨ ;
    infimum = λ c₁ c₂ →
      subInterₗ {c₁ ∧ c₂} {c₁} {c₂} inter∧ ,
      subInterᵣ {c₁ ∧ c₂} {c₁} {c₂} inter∧ ,
      λ c₀ c₀⊑c₁ c₀⊑c₂ →
        ⊑⊑→⊑⋂ {c₀} {c₁ ∧ c₂} {c₁} {c₂} c₀⊑c₁ c₀⊑c₂ inter∧ }

_≋_⋁_ : CCSLExpression
c ≋ c₁ ⋁ c₂ = c₁ ≼≼ c × c₂ ≼≼ c ×
  ∀ {c₀} → c₁ ≼≼ c₀ → c₂ ≼≼ c₀ → c ≼≼ c₀

_≋_⋀_ : CCSLExpression
c ≋ c₁ ⋀ c₂ = c ≼≼ c₁ × c ≼≼ c₂ ×
  ∀ {c₀} → c₀ ≼≼ c₁ → c₀ ≼≼ c₂ → c₀ ≼≼ c

record SpecLattice⋁⋀ (_∧_ _∨_ : Fun₂ WFClock) : Set₁ where
  field
    inter∧ : ∀ {c₁ c₂} → clock (c₁ ∧ c₂) ≋ clock c₁ ⋀ clock c₂
    union∨ : ∀ {c₁ c₂} → clock (c₁ ∨ c₂) ≋ clock c₂ ⋁ clock c₁

specToLattice⋁⋀ : ∀ {_∧_ _∨_}
  → SpecLattice⋁⋀ _∧_ _∨_ → IsLattice _∽ₒ_ _≼≼ₒ_ _∨_ _∧_
specToLattice⋁⋀ {_∧_} {_∨_}
  record { inter∧ = inter∧ ; union∨ = union∨ } =
  record { isPartialOrder = ≼≼-ipo ;
    supremum = λ _ _ → (proj₁ ∘ proj₂) union∨ , proj₁ union∨ ,
      λ _ → flip ((proj₂ ∘ proj₂) union∨) ;
    infimum = λ _ _ → proj₁ inter∧ , (proj₁ ∘ proj₂) inter∧ ,
      λ _ → (proj₂ ∘ proj₂) inter∧}
