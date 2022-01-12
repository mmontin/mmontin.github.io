open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (map to map∑)
open import Data.Maybe hiding (_>>=_)
open import Data.Sum
open import Data.String
open import Data.Nat hiding (_≟_)
open import Data.Unit hiding (_≟_ ; _≤_ ; _≤?_)
open import Function
open import Relation.Nullary
open import Relation.Unary using (Pred) renaming (Decidable to Decidableₚ)
open import Data.List.Relation.Unary.Any renaming (Any to Anyₗ)
open import Data.List.Relation.Unary.All
open import Data.List hiding (_++_ ; all) renaming (map to mapₗ)
open import Data.Nat.Show renaming (show to showℕ)
open import Helper
open import Codata.Musical.Costring
open import IO.Primitive hiding (return ; _>>=_)
open import Data.Maybe.Categorical
open import Category.Monad
open import Agda.Primitive
open import Data.Maybe.Relation.Unary.Any
open import Relation.Nullary.Negation
open import Data.Empty

module Petrinet where

open import ListAssoc String _≟_

record Petrinet : Set where
  constructor [ₘ_-_ₜ][_] ; field
    marking : Map {B = ℕ}
    transitions : Map {B = Map {B = ℕ × ℕ}}
    .conformity : ∀ {t t∈trans p} →
      p ∈ₗ (get t from transitions if t∈trans) → p ∈ₗ marking

open Petrinet

newPet : Petrinet
newPet = [ₘ newMap - newMap ₜ][ (λ { {_} {()}}) ]

+Place : String → ℕ → Petrinet → Maybe Petrinet
+Place s _ [ₘ m - _ ₜ][ _ ] with dec∈ₗ s m
+Place _ _ _ | yes _ = nothing
+Place s n [ₘ m - t ₜ][ c ] | no ¬p =
  just [ₘ put s , n into m when ¬p - t ₜ][ put∈ ∘ c ]

+Trans : String → Petrinet → Maybe Petrinet
+Trans s [ₘ _ - t ₜ][ _ ] with dec∈ₗ s t
+Trans _ _ | yes _ = nothing
+Trans s [ₘ m - t ₜ][ c ] | no ¬p =
  just [ₘ m - put s , newMap into t when ¬p ₜ][
    (λ { {_} {there _} → c}) ]

putpres : ∀ {m₁ : Map {B = ℕ × ℕ}} {m₂ : Map {B = ℕ}} {k v}
  {¬k∈m₁ : ¬ k ∈ₗ m₁} (k∈m₂ : k ∈ₗ m₂) →
  (∀ {x} → x ∈ₗ m₁ → x ∈ₗ m₂) →
  (∀ {x} → x ∈ₗ (put k , v into m₁ when ¬k∈m₁) → x ∈ₗ m₂)
putpres k∈m₂ _ (here refl) = k∈m₂
putpres _ m₁⊑m₂ (there x∈put) = m₁⊑m₂ x∈put

prop₀ : ∀ {m₁ : Map {B = Map {B = ℕ × ℕ}}}
  {m₂ : Map {B = ℕ × ℕ}} {k x} {k∈m₁ x∈assm₁} →
  get x from (assign k , m₂ inside m₁ if k∈m₁) if x∈assm₁ ≡
    get x from m₁ if ∈assign x∈assm₁ ⊎
  get x from (assign k , m₂ inside m₁ if k∈m₁) if x∈assm₁ ≡ m₂
prop₀ {k∈m₁ = here _} {here _} = inj₂ refl
prop₀ {k∈m₁ = here _} {there _} = inj₁ refl
prop₀ {k∈m₁ = there _} {here _} = inj₁ refl
prop₀ {m₁} {k∈m₁ = there k∈m₁} {there x∈assm₁} =
  prop₀ {m₁ = trim m₁ λ ()} {k∈m₁ = k∈m₁} {x∈assm₁}

prop₂ : ∀ {m₁ : Map {B = Map {B = ℕ × ℕ}}}
  {m₂ : Map {B = ℕ}} {m₃ : Map {B = ℕ × ℕ}} {k} {k∈m₁} →
  (∀ {x} → x ∈ₗ m₃ → x ∈ₗ m₂) →
  (∀ {x x∈m₁ p} → p ∈ₗ (get x from m₁ if x∈m₁) → p ∈ₗ m₂) →
  ∀ {x x∈assm₁ p} →
  p ∈ₗ (get x from assign k , m₃ inside m₁ if k∈m₁ if x∈assm₁) →
  p ∈ₗ m₂
prop₂ {m₁} {m₂} {m₃} {k} {k∈m₁} p q {x} {x∈assm₁} {r}
  with prop₀ {m₁} {m₃} {k} {x} {k∈m₁} {x∈assm₁}
prop₂ _ q | inj₁ x₁ rewrite x₁ = q
prop₂ p _ | inj₂ y rewrite y = p

+Arc : String → String → ℕ → ℕ → Petrinet → Maybe Petrinet
+Arc st _ _ _ [ₘ _  - t ₜ][ _ ] with dec∈ₗ st t
+Arc _ _ _ _ _ | no _ = nothing
+Arc _ sp _ _ [ₘ m - _ ₜ][ _ ] | yes _ with dec∈ₗ sp m
+Arc _ _ _ _ _ | yes _ | no _ = nothing
+Arc st sp _ _ [ₘ _ - t ₜ][ _ ] | yes p | yes _
  with dec∈ₗ sp (get st from t if p)
+Arc _ _ _ _ _ | yes _ | yes _ | yes _ = nothing
+Arc st sp -n +n [ₘ m - t ₜ][ c ] | yes p | yes q | no ¬p =
  just [ₘ m - assign st ,
    (put sp , -n , +n into get st from t if p when ¬p) inside t if p ₜ][
    prop₂ {t} {m} (putpres {get st from t if p} {m} {¬k∈m₁ = ¬p} q c) c ]

showₗ : ∀ {a} {A B : Set a} f g → Fun₂ String → List (A × B) → String
showₗ f g h = foldr ((uncurry h ∘ (map∑ f g)) -⟦ _++_ ⟧- ("\n" ++_)) ""

showₚ : List (String × ℕ) → String
showₚ = showₗ id showℕ (λ s₀ s₁ → "pl " ++ s₀ ++ " (" ++ s₁ ++ ")")

Mshowₚ : Map → String
Mshowₚ = showₚ ∘ Map.content

aggregate : List (String × ℕ) → String
aggregate = foldr ((λ {(_ , zero) → "" ; (s , suc zero) → s ++ " " ;
  (s , suc (suc n)) → s ++ "*"
    ++ showℕ (suc (suc n)) ++ " "}) -⟦ _++_ ⟧- id) ""

splito : List (String × (ℕ × ℕ)) → String
splito l = aggregate (mapₗ (λ {(a , b , _) → a , b}) l) ++ " -> " ++
  aggregate (mapₗ (λ {(a , _ , c) → a , c}) l)

splitoₘ : Map → String
splitoₘ = splito ∘ Map.content

showₜ : List (String × Map) → String
showₜ = showₗ id splitoₘ (λ s₀ s₁ → "tr " ++ s₀ ++ " " ++ s₁)

Mshowₜ : Map → String
Mshowₜ = showₜ ∘ Map.content

MPshow : Petrinet → String
MPshow p = Mshowₚ (marking p) ++ "\n" ++ Mshowₜ (transitions p)

MPshowₘ : Maybe Petrinet → String
MPshowₘ (just x) = MPshow x
MPshowₘ nothing = "Unsound net!"

printₚ : Maybe Petrinet → IO ⊤
printₚ = putStrLn ∘ toCostring ∘ MPshowₘ

outₚ : String → Maybe Petrinet → IO ⊤
outₚ name = (writeFile name) ∘ toCostring ∘ MPshowₘ

open RawMonad {lzero} monad

seasons : Maybe Petrinet
seasons = return newPet
  >>= +Place "spring" 1
  >>= +Place "summer" 0
  >>= +Place "winter" 0
  >>= +Place "autumn" 0
  >>= +Trans "s2a"
  >>= +Trans "a2w"
  >>= +Trans "w2s"
  >>= +Trans "s2s"
  >>= +Arc "s2a" "summer" 0 1
  >>= +Arc "s2a" "autumn" 1 0
  >>= +Arc "a2w" "autumn" 0 1
  >>= +Arc "a2w" "winter" 1 0
  >>= +Arc "w2s" "winter" 0 1
  >>= +Arc "w2s" "spring" 1 0
  >>= +Arc "s2s" "spring" 0 1
  >>= +Arc "s2s" "summer" 1 0

deadlock : Maybe Petrinet
deadlock = return newPet
  >>= +Place "waitA" 0
  >>= +Place "waitB" 0
  >>= +Place "A" 1
  >>= +Place "B" 1
  >>= +Place "idle" 2
  >>= +Trans "UseA"
  >>= +Trans "UseB"
  >>= +Trans "UseAB"
  >>= +Trans "UseBA"
  >>= +Arc "UseBA" "A" 1 1
  >>= +Arc "UseBA" "idle" 0 1
  >>= +Arc "UseBA" "B" 0 1
  >>= +Arc "UseBA" "waitA" 1 0
  >>= +Arc "UseB" "waitA" 0 1
  >>= +Arc "UseB" "idle" 1 0
  >>= +Arc "UseB" "B" 1 0
  >>= +Arc "UseAB" "B" 1 1
  >>= +Arc "UseAB" "idle" 0 1
  >>= +Arc "UseAB" "A" 0 1
  >>= +Arc "UseAB" "waitB" 1 0
  >>= +Arc "UseA" "waitB" 0 1
  >>= +Arc "UseA" "idle" 1 0
  >>= +Arc "UseA" "A" 1 0

CanFireArcs : REL Map (List (String × ℕ × ℕ)) _
CanFireArcs m =
  All (_⟨ (λ {(a , -n , _) → Any (-n ≤_) ∘ (get a)}) ⟩ m)

CanFireTrans : REL String Petrinet _
CanFireTrans s [ₘ marking - transitions ₜ][ _ ] =
  Any (CanFireArcs marking ∘ Map.content) (get s transitions)

private

  _≤₀_ : REL ℕ (Maybe ℕ) _
  _≤₀_ x = Any (x ≤_)

  CanFireArc₀ : REL (String × ℕ × ℕ) Map _
  CanFireArc₀ (a , -n , _) = (-n ≤₀_) ∘ (get a)

  CanFireArcs₀ : REL Map (List (String × ℕ × ℕ)) _
  CanFireArcs₀ m = All ( _⟨ CanFireArc₀ ⟩ m)

  CanFireTrans₀ : REL String Petrinet _
  CanFireTrans₀ s [ₘ marking - transitions ₜ][ _ ] =
    Any (CanFireArcs₀ marking ∘ Map.content) (get s transitions)

live : Pred Petrinet _
live pet = ∃ (_⟨ CanFireTrans ⟩ pet)

decFire : Decidable CanFireTrans
decFire _ [ₘ _ - _ ₜ][ _ ] =
  dec ((all λ {_ → dec (_≤?_ _) _}) ∘ Map.content) _

dec≤₀ : Decidable _≤₀_
dec≤₀ x = dec (x ≤?_)

deccfa₀ : Decidable CanFireArc₀
deccfa₀ (a , -n , _) = (dec≤₀ -n) ∘ (get a)

deccfas₀ : Decidable CanFireArcs₀
deccfas₀ m = all λ x → deccfa₀ x m

deccft₀ : Decidable CanFireTrans₀
deccft₀ s [ₘ marking - transitions ₜ][ _ ] =
  dec ((deccfas₀ marking) ∘ Map.content) (get s transitions)

decLive : Decidableₚ live
decLive pet = let t = transitions pet in
  fromSample (keys t) (flip decFire pet)
    (_∘ (prop← {m = t}) ∘ getp {m = t})

fireArcs : ∀ (m : Map {B = ℕ}) {l} → CanFireArcs m l
  → ∃ λ (m' : Map {B = ℕ}) → ∀ {x} → x ∈ₗ m → x ∈ₗ m'
fireArcs m [] = m , id
fireArcs m {l = (a , _ , _) ∷ _} (_ ∷ _) with dec∈ₗ a m
fireArcs m (just _ ∷ p) | yes _ with fireArcs m p
fireArcs m {(a , _ , +n) ∷ _} (just -n≤x ∷ p) | yes q | m' , p' =
  (assign a , (sub -n≤x) + +n inside m' if p' q) , assign∈ ∘ p'

fire_inside_when_ : ∀ s pet → CanFireTrans s pet → Petrinet
fire s inside pet when _ with dec∈ₗ s (transitions pet)
(fire s inside [ₘ m - _ ₜ][ _ ] when just p) | yes _ with fireArcs m p
(fire s inside [ₘ m - t ₜ][ conf ] when just p) | yes _ | m' , q =
  [ₘ m' - t ₜ][ q ∘ conf ]

fire : String → Petrinet → Maybe Petrinet
fire s pet with decFire s pet
fire s pet | yes p = just (fire s inside pet when p)
fire _ _ | no _ = nothing

fireLive : Petrinet → Maybe Petrinet
fireLive pet with decLive pet
fireLive pet | yes (s , p) = just (fire s inside pet when p)
fireLive _ | no _ = nothing

liveness-state : Maybe Petrinet → String
liveness-state nothing = "nothing"
liveness-state (just x) with decLive x
liveness-state (just _) | yes (s , _) = "I can at least fire " ++ s
liveness-state (just _) | no _ = "deadlock"

l-s-d : String
l-s-d = liveness-state deadlock

deadlock₁ : Maybe Petrinet
deadlock₁ = deadlock >>= (fire "UseB")

l-s-d₁ : String
l-s-d₁ = liveness-state deadlock₁

deadlock₂ : Maybe Petrinet
deadlock₂ = deadlock₁ >>= (fire "UseA")

l-s-d₂ : String
l-s-d₂ = liveness-state deadlock₂

deadlock₃ : Maybe Petrinet
deadlock₃ = deadlock₂ >>= (fire "UseAB")

l-s-d₃ : String
l-s-d₃ = liveness-state deadlock₃

