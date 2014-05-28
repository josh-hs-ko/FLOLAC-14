module NatArith where


--------
-- natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

ind : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
ind P z s zero    = z
ind P z s (suc n) = s n (ind P z s n)

ind₁ : (P : ℕ → Set₁) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
ind₁ P z s zero    = z
ind₁ P z s (suc n) = s n (ind₁ P z s n)

infixr 5 _+_

_+_ : ℕ → ℕ → ℕ
_+_ = {!!}

infixr 6 _*_

_*_ : ℕ → ℕ → ℕ
_*_ = {!!}


--------
-- identity types

infix 2 _≡_

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

transport : {A : Set} (P : A → Set) {x : A} → P x → {y : A} → x ≡ y → P y
transport P p refl = p


--------
-- basic properties of identity types

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym = {!!}

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans = {!!}

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong = {!!}


--------
-- Peano axioms

suc-functional : {A : Set} {x y : ℕ} → x ≡ y → suc x ≡ suc y
suc-functional = {!!}

suc-injective : {A : Set} {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-injective = {!!}

data ⊤ : Set where
  unit : ⊤

data ⊥ : Set where

zero-suc-disjoint : (x : ℕ) → suc x ≡ zero → ⊥
zero-suc-disjoint = {!!}  -- hint: use ind₁ (instead of ind)

-- the following six propositions should be automatically typechecked if you define addition and multiplication correctly

add-first-equation : (x : ℕ) → zero + x ≡ x
add-first-equation x = refl

add-second-equation : (x : ℕ) (y : ℕ) → (suc x) + y ≡ suc (x + y)
add-second-equation x y = refl

mult-first-equation : (x : ℕ) → zero * x ≡ zero
mult-first-equation x = refl

mult-second-equation : (x : ℕ) (y : ℕ) → (suc x) * y ≡ y + x * y
mult-second-equation x y = refl

1+1≡2 : suc zero + suc zero ≡ suc (suc zero)
1+1≡2 = refl

2*2≡4 : suc (suc zero) * suc (suc zero) ≡ suc (suc (suc (suc zero)))
2*2≡4 = refl


--------
-- equational reasoning combinators

infixr 1 _≡[_]_

_≡[_]_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡[ q ] q' = trans q q'

infix 2 _∎

_∎ : {A : Set} (x : A) → x ≡ x
x ∎ = refl


--------
-- natural numbers with addition and multiplication form a commutative semi-ring

-- addition is associative

add-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
add-assoc = {!!}

-- addition is commutative

add-comm : (x y : ℕ) → x + y ≡ y + x
add-comm = {!!}

{- Hint: you might need two lemmas
     add-zero : (y : ℕ) → y ≡ y + zero
   and
     add-suc : (y x : ℕ) → suc (y + x) ≡ y + suc x
   which can be proved separately.
-}

-- multiplication left-distributives over addition

left-distr : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
left-distr = {!!}

-- multiplication is commutative

mult-comm : (x y : ℕ) → x * y ≡ y * x
mult-comm = {!!}

-- multiplication right-distributives over addition

right-distr : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
right-distr = {!!}

-- multiplication is associative

mult-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
mult-assoc = {!!}
