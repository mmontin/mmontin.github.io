open import Relation.Binary.Core
open import Relation.Binary
open import Refinement
open import Data.Product
open import Data.Sum hiding (map₂) renaming (swap to swap⊎)
open import Function
open import Helper
open import Relation.Binary.PropositionalEquality
open import Data.Empty

module CCSLRefinement (Support : Set)
  {_≈₁_ _≈₂_ _≺₁_ _≺₂_ : Rel Support _}
  (ispo₁ : IsStrictPartialOrder _≈₁_ _≺₁_)
  (ispo₂ : IsStrictPartialOrder _≈₂_ _≺₂_)
  (refines : (_≈₁_ , _≺₁_) ≺≈ (_≈₂_ , _≺₂_))  where

open import CCSL (record {isStrictPartialOrder = ispo₁}) as ₁
open import CCSL (record {isStrictPartialOrder = ispo₂}) as ₂

≼₁→₂ : ₁._≼_ ⇒ ₂._≼_
≼₁→₂ (inj₁ i≈₁j) = inj₁ (≈₁→₂ refines i≈₁j)
≼₁→₂ (inj₂ i≺₁j) = swap⊎ (≺₁→₂ refines i≺₁j)

_≲₁◅ₙ_ : REL ₁.Clock ₂.Clock _
(Ticks₁ ⌞ _) ≲₁◅ₙ (Ticks₂ ⌞ _) = 
   (∀ (y : ∃ Ticks₂) → ∃ λ (x : ∃ Ticks₁) → x ₂.≈' y) ×
   (∀ (x : ∃ Ticks₁) → ∃ λ (y : ∃ Ticks₂) → y ₂.≈' x)

e∘a≡id : ∀ {c₁ c₂} (p : c₁ ≲₁◅ₙ c₂) → (∀ {i : ∃ (Ticks c₂)} →
  i ₂.≡' (proj₁ ∘ proj₂ p ∘ proj₁ ∘ (proj₁ p)) i)
e∘a≡id (u , _) {i} with u i
e∘a≡id (_ , v) | j , j≈₂i with v j
e∘a≡id {c₂ = c₂} _ {i} | _ , j≈₂i | k , k≈₂j =
  ₂.≈→≡ {c₂} {i} {k} (₂.sym≈ (₂.trans≈ k≈₂j j≈₂i))

⊑≲₁◅ₙ : ∀ {c₁₁ c₁₂ c₂₁ c₂₂} →
  c₁₁ ₁.⊑ c₁₂ → c₁₁ ≲₁◅ₙ c₂₁ → c₁₂ ≲₁◅ₙ c₂₂ → c₂₁ ₂.⊑ c₂₂
⊑≲₁◅ₙ o (p , _) (_ , s) i₂₁ = (i₂₁ , ₂.refl≈)
  >[ id -⟦ ₂.trans≈ ⟧- ₂.sym≈ ]> p
  >[ id -⟦ ₂.trans≈ ⟧- ≈₁→₂ refines ]> o
  >[ id -⟦ ₂.trans≈ ⟧- ₂.sym≈ ]> s

♯≲₁◅ₙ : ∀ {c₁₁ c₁₂ c₂₁ c₂₂} →
  c₂₁ ₂.♯ c₂₂ → c₁₁ ≲₁◅ₙ c₂₁ → c₁₂ ≲₁◅ₙ c₂₂ → c₁₁ ₁.♯ c₁₂
♯≲₁◅ₙ p (q , r) (s , t) x y x≈₁y with r x | t y
♯≲₁◅ₙ p (q , r) (s , t) x y x≈₁y | rx , rx≈₂x | ty , ty≈₂y =
  p rx ty (₂.trans≈ (₂.trans≈ rx≈₂x (≈₁→₂ refines x≈₁y)) (₂.sym≈ ty≈₂y))

⋃≲₁◅ₙ : ∀ {c₁₁ c₁₀ c₁₂ c₂} →
  c₁₁ ≲₁◅ₙ c₂ → c₁₂ ≲₁◅ₙ c₂ → c₁₀ ₁.≋ c₁₁ ⋃ c₁₂ → c₁₀ ≲₁◅ₙ c₂
⋃≲₁◅ₙ (p , _) _ (_ , u) .proj₁ x = (x , ₂.refl≈)
  >[ flip ₂.trans≈ ]> p
  >[ id -⟦ flip ₂.trans≈ ⟧- (₂.sym≈ ∘ ≈₁→₂ refines) ]> u ∘ map₂ inj₁
⋃≲₁◅ₙ _ _ (t , _) .proj₂ x with t x
⋃≲₁◅ₙ (_ , q) _ _ .proj₂ _ | ((i , inj₁ tc₁₁i) , i≈₁x) =
  ((i , tc₁₁i) , ≈₁→₂ refines i≈₁x) >[ flip ₂.trans≈ ]> q
⋃≲₁◅ₙ _ (_ , s) _ .proj₂ _ | ((i , inj₂ tc₁₂i) , i≈₁x) =
  ((i , tc₁₂i) , ≈₁→₂ refines i≈₁x) >[ flip ₂.trans≈ ]> s

∽≲₁◅ₙ : ∀ {c₁ c₂₁ c₂₂} → c₁ ≲₁◅ₙ c₂₁ → c₁ ≲₁◅ₙ c₂₂ → c₂₁ ₂.∽ c₂₂
∽≲₁◅ₙ (p , _) (_ , s) .proj₁ x = (x , ₂.refl≈)
  >[ id -⟦ ₂.trans≈ ⟧- ₂.sym≈ ]> p
  >[ id -⟦ ₂.trans≈ ⟧- ₂.sym≈ ]> s
∽≲₁◅ₙ (_ , q) (r , _) .proj₂ x = (x , ₂.refl≈)
  >[ id -⟦ ₂.trans≈ ⟧- ₂.sym≈ ]> r
  >[ id -⟦ ₂.trans≈ ⟧- ₂.sym≈ ]> q

_≲₁◅₁_ : REL ₁.Clock ₂.Clock _
(Ticks₁ ⌞ _) ≲₁◅₁ (Ticks₂ ⌞ _) = 
   (∀ (y : ∃ Ticks₂) → ∃! (₁._≈'_) λ (x : ∃ Ticks₁) → x ₂.≈' y) ×
   (∀ (x : ∃ Ticks₁) → ∃ λ (y : ∃ Ticks₂) → y ₂.≈' x)

≲→≲₁◅₁ : ∀ {c₁ c₂} → c₁ ≲₁◅₁ c₂ → c₁ ≲₁◅ₙ c₂
≲→≲₁◅₁ (p , q) = ∃!→∃ ∘ p , q

≲₁◅₁→≈₂→₁ : ∀ {c₁₁ c₂₁} → c₁₁ ≲₁◅₁ c₂₁ → {k l : ∃ (Ticks c₁₁)}
  → k ₂.≈' l → k ₁.≈' l
≲₁◅₁→≈₂→₁ {c₁₁} {c₂₁} (p , q) {k} {l} k≈₂l with q k | q l
... | u , u≈₂k | v , v≈₂l with ₂.≈→≡ {c₂₁} {u} {v}
  (₂.trans≈ (₂.trans≈ u≈₂k k≈₂l) (₂.sym≈ v≈₂l))
... | refl with p u
... | j , j≈₂u , ∃! =
  ₁.trans≈ (₁.sym≈ (∃! {k} (₂.sym≈ u≈₂k))) (∃! {l} (₂.sym≈ v≈₂l))

≲₁◅₁→≺₁→₂ : ∀ {c₁₁ c₂₁} → c₁₁ ≲₁◅₁ c₂₁ → {k l : ∃ (Ticks c₁₁)}
  → k ₁.≺' l → k ₂.≺' l
≲₁◅₁→≺₁→₂ {c₁₁} {c₂₁} p {k} {l} k≺₁l with ≺₁→₂ refines k≺₁l
... | inj₁ k≺₂l = k≺₂l
... | inj₂ k≈₂l =
  ⊥-elim (₁.irrefl≈≺ (≲₁◅₁→≈₂→₁ {c₁₁} {c₂₁} p {k} {l} k≈₂l) k≺₁l)

a∘e≡id : ∀ {c₁ c₂} (p : c₁ ≲₁◅₁ c₂) → (∀ {i : ∃ (Ticks c₁)} →
  i ₂.≡' (proj₁ ∘ proj₁ p ∘ proj₁ ∘ (proj₂ p)) i)
a∘e≡id (_ , v) {i} with v i
a∘e≡id (u , _) | j , j≈₂i with u j
a∘e≡id {c₁} {c₂} p {i} | j , j≈₂i | k , k≈₂j , _ =
  ₁.≈→≡ {c₁} {i} {k} (≲₁◅₁→≈₂→₁ {c₁} {c₂} p {i} {k}
    (₂.sym≈ (₂.trans≈ k≈₂j j≈₂i)))

≺≺₂→≺≺₁ : ∀ {c₁₁ c₁₂ c₂₁ c₂₂} → c₁₁ ≲₁◅₁ c₂₁ → c₁₂ ≲₁◅₁ c₂₂
  → c₂₁ ₂.≺≺ c₂₂ → c₁₁ ₁.≺≺ c₁₂

≺≺₂→≺≺₁ (p , _) (_ , q₁) prec .h = proj₁ ∘ p ∘ h prec ∘ proj₁ ∘ q₁
≺≺₂→≺≺₁ {c₁₁} {_} {c₂₁} (p , q) (_ , q₁) prec .congruent {i} {j} i≈₁j
  with q₁ i | q₁ j ; ... | i₁ , i₁≈₂i | j₁ , j₁≈₂j with p (h prec i₁) | p (h prec j₁)
... | i₃ , i₃≈₂i₂ , _ | j₃ , j₃≈₂j₂ , _ with ≈₁→₂ refines i≈₁j
... | i≈₂j with ₂.trans≈ (₂.trans≈ i₁≈₂i i≈₂j) (₂.sym≈ j₁≈₂j)
... | i₁≈₂j₁ with congruent prec {i₁} {j₁} i₁≈₂j₁
... | i₂≈₂j₂ with ₂.trans≈ i₃≈₂i₂ (₂.trans≈ i₂≈₂j₂ (₂.sym≈ j₃≈₂j₂))
... | i₃≈₂j₃ = ≲₁◅₁→≈₂→₁ {c₁₁} {c₂₁} (p , q) {i₃} {j₃} i₃≈₂j₃
≺≺₂→≺≺₁ (p , _) (_ , q₁) prec .precedes i with q₁ i
... | j , j≈₂i with p (h prec j)
... | _ , k≈₂hj , _ with precedes prec j
... | hj≺₂j with ₂.≺≈≈→≺ hj≺₂j (₂.sym≈ k≈₂hj) j≈₂i
... | k≺₂i = ≺₂→₁ refines k≺₂i
≺≺₂→≺≺₁ {_} {c₁₂} {_} {c₂₂} _ q _ .preserves {i} {j} i≺₁j
  with ≲₁◅₁→≺₁→₂ {c₁₂} {c₂₂} q {i} {j} i≺₁j
≺≺₂→≺≺₁ (p , _) (_ , q₁) prec .preserves {i} {j} _ | i≺₂j with q₁ i | q₁ j
... | i₁ , i₁≈i | j₁ , j₁≈j  with p (h prec i₁) | p (h prec j₁)
... | _ , i₃≈₂i₂ , _ | _ , j₃≈₂j₂ , _
  with ₂.≺≈≈→≺ i≺₂j (₂.sym≈ i₁≈i) (₂.sym≈ j₁≈j)
... | i₁≺₂j₁ with preserves prec {i₁} {j₁} i₁≺₂j₁
... | i₂≺₂j₂ with ₂.≺≈≈→≺ i₂≺₂j₂ (₂.sym≈ i₃≈₂i₂) (₂.sym≈ j₃≈₂j₂)
... | i₃≺₂j₃ = ≺₂→₁ refines i₃≺₂j₃
≺≺₂→≺≺₁ {c₁₁} {c₁₂} {c₂₁} {c₂₂} (p , q) (p₁ , q₁) prec .dense
  {i₀} {j₀} {k₃} i₃≺₁k₃ k₃≺₁j₃ with q₁ i₀ | q₁ j₀ | q k₃
... | i₁ , i₁≈₂i | j₁ , j₁≈₂j | k₂ , k₂≈₂k₃
  with p (h prec i₁) | p (h prec j₁)
... | i₃ , i₃≈₂i₂ , _ | j₃ , j₃≈₂j₂ , _
  with ≲₁◅₁→≺₁→₂ {c₁₁} {c₂₁} (p , q) {i₃} {k₃} i₃≺₁k₃
... | i₃≺₂k₃ with ≲₁◅₁→≺₁→₂ {c₁₁} {c₂₁} (p , q) {k₃} {j₃} k₃≺₁j₃
... | k₃≺₂j₃ with ₂.≺≈≈→≺ i₃≺₂k₃ i₃≈₂i₂ (₂.sym≈ k₂≈₂k₃)
... | i₂≺₂k₂ with ₂.≺≈≈→≺ k₃≺₂j₃ (₂.sym≈ k₂≈₂k₃) j₃≈₂j₂
... | k₂≺₂j₂ with dense prec {i₁} {j₁} {k₂} i₂≺₂k₂ k₂≺₂j₂
... | k₁ , hk₁≈₂k₂ with p₁ k₁
... | k₀ , k₀≈₂k₁ , _ with ₂.trans≈ (proj₂ (q₁ k₀)) k₀≈₂k₁
... | qk₀≈₂k₁ with congruent prec {proj₁ (q₁ k₀)} {k₁} qk₀≈₂k₁
... | hqk₀≈₂hk₁ with ₂.trans≈ (₂.trans≈ hqk₀≈₂hk₁ hk₁≈₂k₂) k₂≈₂k₃
... | hqk₀≈₂k₃ with ₂.trans≈
  (proj₁ (proj₂ (p (h prec (proj₁ (q₁ k₀)))))) hqk₀≈₂k₃
... | phqk₀≈₂k₃ = k₀ , ≲₁◅₁→≈₂→₁ {c₁₁} {c₂₁} (p , q)
  {proj₁ (p (h prec (proj₁ (q₁ k₀))))} {k₃} phqk₀≈₂k₃

prec₁→≼≼₂ : ∀ {c₁₁ c₁₂ c₂₁ c₂₂} {_R_ : Rel ₁.Support _}
  → _R_ ⇒ ₁._≼_ → c₁₁ ≲₁◅₁ c₂₁ → c₁₂ ≲₁◅₁ c₂₂
  → ₁.Precedence _R_ c₁₁ c₁₂ → c₂₁ ₂.≼≼ c₂₂

prec₁→≼≼₂ _ (p , q) (p₁ , q₁) prec .h = proj₁ ∘ q ∘ h prec ∘ proj₁ ∘ p₁
prec₁→≼≼₂ {_} {c₁₂} {_} {c₂₂} _ (p , q) (p₁ , q₁) prec .congruent
  {i₀} {j₀} i₀≈₂j₀ with p₁ i₀ | p₁ j₀
... | i₁ , i₁≈₂i₀ , _ | j₁ , j₁≈₂j₀ , _ with q (h prec i₁) | q (h prec j₁)
... | i₃ , i₃≈₂hi₁ | j₃ , j₂≈₂hj₁
  with ₂.trans≈ i₁≈₂i₀ (₂.trans≈ i₀≈₂j₀ (₂.sym≈ j₁≈₂j₀))
... | i₁≈₂j₁ with ≲₁◅₁→≈₂→₁ {c₁₂} {c₂₂} (p₁ , q₁) {i₁} {j₁} i₁≈₂j₁
... | i₁≈₁j₁ with ≈₁→₂ refines (congruent prec {i₁} {j₁} i₁≈₁j₁)
... | hi₁≈₂hj₁ = ₂.trans≈ i₃≈₂hi₁ (₂.trans≈ hi₁≈₂hj₁ (₂.sym≈ j₂≈₂hj₁))
prec₁→≼≼₂ R⇒≼₁ (p , q) (p₁ , q₁) prec .precedes i₀ with p₁ i₀
... | i₁ , i₁≈₂i₀ , _ with precedes prec i₁
... | hi₁Ri₁ with ≼₁→₂ (R⇒≼₁ hi₁Ri₁) 
... | hi₁≼₂i₁ with q (h prec i₁)
... | i₃ , i₃≈₂hi₁ = ₂.trans≼ (inj₁ i₃≈₂hi₁) (₂.trans≼ hi₁≼₂i₁ (inj₁ i₁≈₂i₀))
prec₁→≼≼₂ {c₁₁} {_} {c₂₁} _ (p , q) (p₁ , q₁) prec .preserves
  {i₀} {j₀} i₀≺₂j₀ with p₁ i₀ | p₁ j₀
... | i₁ , i₁≈₂i₀ , _ | j₁ , j₁≈₂j₀ , _ with q (h prec i₁) | q (h prec j₁)
... | i₃ , i₃≈₂hi₁ | j₃ , j₂≈₂hj₁
  with ₂.≺≈≈→≺ i₀≺₂j₀ (₂.sym≈ i₁≈₂i₀) (₂.sym≈ j₁≈₂j₀)
... | i₁≺₂j₁ with ≺₂→₁ refines i₁≺₂j₁
... | i₁≺₁j₁ with preserves prec {i₁} {j₁} i₁≺₁j₁
... | hi₁≺₁hj₁ with
  ≲₁◅₁→≺₁→₂ {c₁₁} {c₂₁} (p , q) {h prec i₁} {h prec j₁} hi₁≺₁hj₁
... | hi₁≺₂hj₁ = ₂.≺≈≈→≺ hi₁≺₂hj₁ (₂.sym≈ i₃≈₂hi₁) (₂.sym≈ j₂≈₂hj₁)
prec₁→≼≼₂ {_} {c₁₂} {_} {c₂₂} _ (p , q) (p₁ , q₁) prec .dense
  {i₀} {j₀} {k₃} i₃≺₂k₃ k₃≺₂j₃ with p₁ i₀ | p₁ j₀ | p k₃
... | i₁ , i₁≈₂i₀ , _ | j₁ , j₁≈₂j₀ , _ | k₂ , k₂≈₂k₃ , _
  with q (h prec i₁) | q (h prec j₁)
... | i₃ , i₃≈₂i₂ | j₃ , j₃≈₂j₂
  with ≺₂→₁ refines (₂.≺≈≈→≺ i₃≺₂k₃ i₃≈₂i₂ (₂.sym≈ k₂≈₂k₃))
... | i₂≺₁k₂ with ≺₂→₁ refines (₂.≺≈≈→≺ k₃≺₂j₃ (₂.sym≈ k₂≈₂k₃) j₃≈₂j₂)
... | k₂≺₁j₂ with dense prec {i₁} {j₁} {k₂} i₂≺₁k₂ k₂≺₁j₂
... | k₁ , hk₁≈₁k₂ with q₁ k₁
... | k₀ , k₀≈₂k₁ with ₂.trans≈ (proj₁ (proj₂ (p₁ k₀))) k₀≈₂k₁
... | pk₀≈₂k₁
  with ≲₁◅₁→≈₂→₁ {c₁₂} {c₂₂} (p₁ , q₁) {proj₁ (p₁ k₀)} {k₁} pk₀≈₂k₁
... | pk₀≈₁k₁ with congruent prec {proj₁ (p₁ k₀)} {k₁} pk₀≈₁k₁
... | hpk₀≈₁hk₁ with ₂.trans≈ (₂.trans≈ (≈₁→₂ refines hpk₀≈₁hk₁)
  (≈₁→₂ refines hk₁≈₁k₂)) k₂≈₂k₃
... | hpk₀≈₂k₃ = k₀ , ₂.trans≈ (proj₂ (q (h prec (proj₁ (p₁ k₀))))) hpk₀≈₂k₃

≺≺₁→≼≼₂ : ∀ {c₁₁ c₁₂ c₂₁ c₂₂} → c₁₁ ≲₁◅₁ c₂₁ → c₁₂ ≲₁◅₁ c₂₂
  → c₁₁ ₁.≺≺ c₁₂ → c₂₁ ₂.≼≼ c₂₂
≺≺₁→≼≼₂ = prec₁→≼≼₂ inj₂

≼≼₁→≼≼₂ : ∀ {c₁₁ c₁₂ c₂₁ c₂₂} → c₁₁ ≲₁◅₁ c₂₁ → c₁₂ ≲₁◅₁ c₂₂
  → c₁₁ ₁.≼≼ c₁₂ → c₂₁ ₂.≼≼ c₂₂
≼≼₁→≼≼₂ = prec₁→≼≼₂ id
