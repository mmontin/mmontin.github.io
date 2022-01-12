open import Data.String
open import Data.Nat hiding (_≟_ ; pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Sum
open import Relation.Nullary.Negation
open import Relation.Nullary.Product
open import Data.Product
open import Data.Sum
open import Data.Product.Properties
open import Function
open import Data.Maybe hiding (_>>=_) renaming (map to mapₘ)
open import Data.Maybe.Relation.Unary.Any
open import Data.Bool hiding (_≟_)
open import Data.List.Relation.Unary.Any renaming (Any to Anyₗ)
open import Data.List.Relation.Unary.All
open import Data.List renaming (map to mapₗ) hiding (all)
open import Relation.Unary renaming (Decidable to Decidableₚ)
open import Data.Maybe.Categorical
open import Category.Monad
open import Agda.Primitive
open import Helper

module SimplePDL where

data WDState : Set where
  notStarted : WDState
  inProgress : WDState
  finished   : WDState

open WDState

data Action : Set where
  start : Action
  finish : Action

open Action

data Dependence : Set where
  toStart : ∀ (a : Action) → Dependence
  toFinish : ∀ (a : Action) → Dependence

WorkSequence : Set
WorkSequence = String × Dependence × String

_≟d_ : Decidable {A = Dependence} _≡_
toStart start ≟d toStart start = yes refl
toStart start ≟d toStart finish = no λ ()
toStart start ≟d toFinish _ = no λ ()
toStart finish ≟d toStart start = no λ ()
toStart finish ≟d toStart finish = yes refl
toStart finish ≟d toFinish _ = no λ ()
toFinish start ≟d toStart _ = no λ ()
toFinish start ≟d toFinish start = yes refl
toFinish start ≟d toFinish finish = no λ ()
toFinish finish ≟d toStart _ = no λ ()
toFinish finish ≟d toFinish start = no λ ()
toFinish finish ≟d toFinish finish = yes refl

dec≡ws : Decidable {A = WorkSequence} _≡_
dec≡ws = ≡-dec _≟_ (≡-dec _≟d_ _≟_)

open import ListAssoc String _≟_ {B = WDState}
open import ListUnique WorkSequence dec≡ws using (Bag ; newBag)
  renaming
    (_∈ₗ_ to _∈g_ ; dec∈ₗ to dec∈g ; put_into_when_ to putg_into_when_)

record SimplePDL : Set where
  constructor pdl ; field
    wds : Map
    wss : Bag 
    .conf₁ : ∀ {x} → x ∈g wss → proj₁ x ∈ₗ wds
    .conf₂ : ∀ {x} → x ∈g wss → proj₂ (proj₂ x) ∈ₗ wds
    .conf₃ : ∀ {x} → x ∈g wss → ¬ proj₁ x ≡ (proj₂ (proj₂ x))

  module _ where
  
  open import ListUnique as LU using (Bag)

  record WorkSequence' (m : Map) : Set where
    field
      predecessor : String
      successor : String
      dependence : Dependence
      .p∈m : predecessor ∈ₗ m
      .s∈m : successor ∈ₗ m
      .¬≡ : ¬ predecessor ≡ successor

  open WorkSequence'

  dec≡ws' : ∀ {m} → Decidable {A = WorkSequence' m} _≡_
  dec≡ws' w₁ w₂ with predecessor w₁ ≟ predecessor w₂
  dec≡ws' w₁ w₂ | yes p with successor w₁ ≟ successor w₂
  dec≡ws' w₁ w₂ | yes p | yes q with dependence w₁ ≟d dependence w₂
  dec≡ws' record { predecessor = .p ; successor = .s ; dependence = .d}
    record { predecessor = p ; successor = s ; dependence = d}
      | yes refl | yes refl | yes refl = yes refl
  dec≡ws' _ _ | yes _ | yes _ | no ¬p = no λ {refl → ¬p refl}
  dec≡ws' _ _ | yes _ | no ¬p = no λ {refl → ¬p refl}
  dec≡ws' _ _ | no ¬p = no λ {refl → ¬p refl}

  SimplePDL' : Set
  SimplePDL' = ∃ λ x → LU.Bag (WorkSequence' x) dec≡ws'

open SimplePDL

newPDL : SimplePDL
newPDL = pdl newMap newBag (λ ()) (λ ()) (λ ())

+wd : String → SimplePDL → Maybe SimplePDL
+wd s (pdl wds _ _ _ _) with dec∈ₗ s wds
+wd _ _ | yes _ = nothing
+wd s (pdl wds wss c₁ c₂ c₃) | no ¬p = just (pdl (put s ,
  notStarted into wds when ¬p) wss (put∈ ∘ c₁) (put∈ ∘ c₂) c₃)

toWsk : String → Maybe Dependence
toWsk s with s ≟ "s2s"
toWsk s | no _ with s ≟ "s2f"
toWsk s | no _ | no _ with s ≟ "f2s"
toWsk s | no _ | no _ | no _ with s ≟ "f2f"
toWsk s | no _ | no _ | no _ | no _ = nothing
toWsk s | no _ | no _ | no _ | yes _ = just (toFinish finish)
toWsk s | no _ | no _ | yes _ = just (toStart finish)
toWsk _ | no _ | yes _ = just (toFinish start)
toWsk _ | yes _ = just (toStart start)

+ws : String → String → String → SimplePDL → Maybe SimplePDL
+ws _ kind _ _ with toWsk kind
+ws _ _ _ _ | nothing = nothing
+ws pred _ succ _ | just _ with pred ≟ succ
+ws _ _ _ _ | just _ | yes _ = nothing
+ws pred _ _ xpdl | just _ | no _ with dec∈ₗ pred (wds xpdl)
+ws _ _ succ xpdl | just _ | no _ | yes _ with dec∈ₗ succ (wds xpdl)
+ws pred _ succ xpdl | just x | no _ | yes _ | yes _
  with dec∈g (pred , x , succ) (wss xpdl)
+ws pred _ succ (pdl wds wss c₁ c₂ c₃) |
  just x | no ¬p | yes q | yes r | no ¬p₁ =
  just (pdl wds (putg pred , x , succ into wss when ¬p₁)
  (λ {(here refl) → q ; (there x₁) → c₁ x₁})
  (λ {(here refl) → r ; (there x₁) → c₂ x₁})
  λ {(here refl) → ¬p ; (there x₁) → c₃ x₁})
+ws _ _ _ _ | just _ | no _ | yes _ | yes _ | yes _ = nothing
+ws _ _ _ _ | just _ | no _ | yes _ | no _ = nothing
+ws _ _ _ _ | just _ | no _ | no _ = nothing

Complies← : Action → WDState → Set
Complies← start wds = wds ≡ inProgress ⊎ wds ≡ finished
Complies← finish = _≡ finished

Complies→ : Action → WDState → Set
Complies→ start = _≡ notStarted
Complies→ finish = _≡ inProgress

data Comp (wds : WDState) : Action → Dependence → Set where
  cStart : ∀ {a} → Complies← a wds → Comp wds start (toStart a)
  cFinish : ∀ {a} → Complies← a wds → Comp wds finish (toFinish a)
  cStartFinish : ∀ {a} → Comp wds start (toFinish a)
  cFinishStart : ∀ {a} → Comp wds finish (toStart a)

CompliesWithList : Action → String → Map → List WorkSequence → Set
CompliesWithList a s wds =
  All λ {(prec , dep , succ) → (¬ succ ≡ s) ⊎
  Any (λ x → Comp x a dep) (get prec wds)}

CompliesWith : Action → String → SimplePDL → Set
CompliesWith a s (pdl wds wss _ _ _) =
  Any (Complies→ a) (get s wds) ×
    CompliesWithList a s wds (Bag.content wss)

AliveAction : Action → SimplePDL → Set
AliveAction a spdl = ∃ (λ s → CompliesWith a s spdl)

Alive : SimplePDL → Set
Alive = AliveAction start ∪ AliveAction finish 

decatpf : Decidable Complies←
decatpf start notStarted = no (λ {(inj₁ ()) ; (inj₂ ())})
decatpf start inProgress = yes (inj₁ refl)
decatpf start finished = yes (inj₂ refl)
decatpf finish notStarted = no λ ()
decatpf finish inProgress = no λ ()
decatpf finish finished = yes refl

decatpt : Decidable Complies→
decatpt start notStarted = yes refl
decatpt start inProgress = no λ ()
decatpt start finished = no λ ()
decatpt finish notStarted = no λ ()
decatpt finish inProgress = yes refl
decatpt finish finished = no λ ()

deccomp : ∀ {wds} → Decidable (Comp wds)
deccomp {wds} _ (toStart a') with decatpf a' wds
deccomp start (toStart _) | yes p = yes (cStart p)
deccomp finish (toStart _) | yes _ = yes cFinishStart
deccomp start (toStart _) | no ¬p = no (λ {(cStart x) → ¬p x})
deccomp finish (toStart _) | no _ = yes cFinishStart
deccomp {wds} _ (toFinish a') with decatpf a' wds
deccomp start (toFinish _) | no _ = yes cStartFinish
deccomp finish (toFinish _) | no ¬p = no (λ {(cFinish x) → ¬p x})
deccomp start (toFinish _) | yes _ =  yes cStartFinish
deccomp finish (toFinish _) | yes p = yes (cFinish p)

deccwl : ∀ {a s} → Decidable (CompliesWithList a s)
deccwl wds = all λ _ → ¬? (_ ≟ _) ⊎-dec dec (λ _ → deccomp _ _) _

deccw : ∀ {a} → Decidable (CompliesWith a)
deccw {a} _ spdl = dec (decatpt a) _ ×-dec deccwl (wds spdl) _

decAliveAction : ∀ a → Decidableₚ (AliveAction a)
decAliveAction a spdl = let w = wds spdl in
  fromSample (keys w) (flip deccw spdl)
    (_∘ (prop← {m = w}) ∘ (getp {m = w}) ∘ proj₁)

decAlive : Decidableₚ Alive
decAlive x = decAliveAction start x ⊎-dec decAliveAction finish x

perform_from_when_ : ∀ (a : Action) (wds : WDState) →
  Complies→ a wds → WDState
perform start from .notStarted when refl = inProgress
perform finish from .inProgress when refl = finished

perform_on_inside_when_ : ∀ a s pdl →
  CompliesWith a s pdl → SimplePDL
perform a on s inside spdl when (fst , snd) with dec∈ₗ s (wds spdl)
perform a on s inside pdl wds wss c₁ c₂ c₃ when (just q , snd) | yes p =
  pdl (assign s ,
    (perform a from (get s from wds if p) when q) inside wds if p)
    wss (assign∈ ∘ c₁) (assign∈ ∘ c₂) c₃

perform : ∀ a s pdl → Maybe SimplePDL
perform a s spdl with deccw {a} s spdl
perform _ _ _ | no _ = nothing
perform a s spdl | yes p = just (perform a on s inside spdl when p)

start_inside_ : ∀ s pdl → Maybe SimplePDL
start_inside_ = perform start

finish_inside_ : ∀ s pdl → Maybe SimplePDL
finish_inside_ = perform finish

open RawMonad {lzero} monad

dev : Maybe SimplePDL
dev = return newPDL
  >>= +wd "Documentation"
  >>= +wd "Design"
  >>= +wd "Programming"
  >>= +wd "Testing"
  >>= +ws "Design" "f2f" "Documentation"
  >>= +ws "Design" "s2s" "Documentation"
  >>= +ws "Design" "f2s" "Programming"
  >>= +ws "Design" "s2s" "Testing"
  >>= +ws "Programming" "f2f" "Testing"

listCanPerform : ∀ a spdl → (candidates : List String) → List String
listCanPerform _ _ [] = []
listCanPerform a spdl (s ∷ _) with deccw {a} s spdl
listCanPerform a spdl (_ ∷ l) | no _ = listCanPerform a spdl l
listCanPerform a spdl (s ∷ l) | yes p = s ∷ (listCanPerform a spdl l)

listCanStart : ∀ spdl → List String
listCanStart spdl = listCanPerform start spdl (keys (wds spdl))

listCanFinish : ∀ spdl → List String
listCanFinish spdl = listCanPerform finish spdl (keys (wds spdl))

csdev : mapₘ listCanStart dev ≡ just ("Design" ∷ [])
csdev = refl

dev₁ : _
dev₁ = dev >>= start "Design" inside_

csdev₁ : mapₘ listCanStart dev₁ ≡
  just ("Testing" ∷ "Documentation" ∷ [])
csdev₁ = refl

cfdev₁ : mapₘ listCanFinish dev₁ ≡ just ("Design" ∷ [])
cfdev₁ = refl

dev₂ : _
dev₂ = dev₁ >>= finish "Design" inside_

csdev₂ : mapₘ listCanStart dev₂ ≡
  just ("Testing" ∷ "Programming" ∷ "Documentation" ∷ [])
csdev₂ = refl

cfdev₂ :  mapₘ listCanFinish dev₂ ≡ just []
cfdev₂ = refl
