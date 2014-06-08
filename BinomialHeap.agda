open import Data.Sum

module BinomialHeap (V : Set) (_≤_ : V → V → Set) (_≤?_ : (x y : V) → x ≤ y ⊎ y ≤ x) where

open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Bin : Set where  -- specialisation of List Bool
  nul  :       Bin
  zero : Bin → Bin
  one  : Bin → Bin

incr : Bin → Bin
incr nul      = one nul
incr (zero b) = one b
incr (one  b) = zero (incr b)

data Nat : Set where
  zero :       Nat
  suc  : Nat → Nat

data Unit : Set where
 unit : Unit

_^_ : (Nat → Set) → Nat → Set
X ^ zero    = Unit
X ^ (suc n) = X n × (X ^ n)

-- BTree ^ r = BTree (r - 1) × BTree (r - 2) × ... × BTree 0

data BTree : V → Nat → Set where
  node : {x : V} {r : Nat} (y : V) {{ord : x ≤ y}} (ts : BTree y ^ r) → BTree x r

if_then_else_ : {A B C : Set} → A ⊎ B → ({{_ : A}} → C) → ({{_ : B}} → C) → C
if inj₁ a then t else u = t
if inj₂ b then t else u = u

attach' : {x y : V} {r : Nat} → BTree x r → BTree y r → Σ[ z ∈ V ] BTree z (suc r)
attach' {x} {y} (node a ts) (node b us) = if a ≤? b then (x , node a (node b us , ts)) else (y , node b (node a ts , us))

attach : {x y : V} {r : Nat} (t : BTree x r) (u : BTree y r) → BTree (proj₁ (attach' t u)) (suc r)
attach t u = proj₂ (attach' t u)

-- BHeap r ∋ dʳ dʳ⁺¹ dʳ⁺² ...

data BHeap : Nat → Set where
  nul  : {r : Nat} →                                     BHeap r
  zero : {r : Nat} →                     BHeap (suc r) → BHeap r
  one  : {r : Nat} {x : V} → BTree x r → BHeap (suc r) → BHeap r

{-

insT : {x : V} {r : Nat} → BTree x r → BHeap r → BHeap r
insT t nul       = one t nul
insT t (zero  h) = nul  -- ?!
insT t (one u h) = zero (insT (attach t u) h)

-}

-- free
toBin : {r : Nat} → BHeap r → Bin
toBin nul       = nul
toBin (zero  h) = zero (toBin h)
toBin (one x h) = one  (toBin h)

-- free
data BHeap' : Nat → Bin → Set where
  nul  : {r : Nat} →                                                  BHeap' r nul
  zero : {r : Nat} {b : Bin} →                     BHeap' (suc r) b → BHeap' r (zero b)
  one  : {r : Nat} {b : Bin} {x : V} → BTree x r → BHeap' (suc r) b → BHeap' r (one  b)

insT' : {x : V} {r : Nat} {b : Bin} → BTree x r → BHeap' r b → BHeap' r (incr b)
insT' t nul       = one t nul
insT' t (zero  h) = one t h
insT' t (one u h) = zero (insT' (attach t u) h)

-- free
toBHeap : {r : Nat} {b : Bin} → BHeap' r b → BHeap r
toBHeap nul       = nul
toBHeap (zero  h) = zero  (toBHeap h)
toBHeap (one t h) = one t (toBHeap h)

-- free
fromBHeap : {r : Nat} (h : BHeap r) → BHeap' r (toBin h)
fromBHeap nul       = nul
fromBHeap (zero  h) = zero  (fromBHeap h)
fromBHeap (one t h) = one t (fromBHeap h)

-- free
insT : {x : V} {r : Nat} → BTree x r → BHeap r → BHeap r
insT t h = toBHeap (insT' t (fromBHeap h))

-- free
recomputation : {r : Nat} {b : Bin} (h : BHeap' r b) → toBin (toBHeap h) ≡ b
recomputation nul       = refl
recomputation (zero  h) = cong zero (recomputation h)
recomputation (one t h) = cong one  (recomputation h)

_≐_ : {A B : Set} (f g : A → B) → Set
f ≐ g = ∀ x → f x ≡ g x

infix 2 _≐_

-- free
coherence : {x : V} {r : Nat} (t : BTree x r) → toBin ∘ insT t ≐ incr ∘ toBin
coherence t h = recomputation (insT' t (fromBHeap h))
