module NatArithC where


--------
-- natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
-- for Agda < 2.4.0
-- {-# BUILTIN ZERO zero #-}
-- {-# BUILTIN SUC  suc  #-}

ind : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
ind P z s zero    = z
ind P z s (suc n) = s n (ind P z s n)

ind₁ : (P : ℕ → Set₁) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
ind₁ P z s zero    = z
ind₁ P z s (suc n) = s n (ind₁ P z s n)

pred : ℕ → ℕ
pred = ind (λ _ → ℕ) zero (λ n _ → n)

infixr 5 _+_

_+_ : ℕ → ℕ → ℕ
_+_ = ind (λ _ → ℕ → ℕ) (λ n → n) (λ _ f n → suc (f n))

infixr 6 _*_

_*_ : ℕ → ℕ → ℕ
_*_ = ind (λ _ → ℕ → ℕ) (λ _ → zero) (λ _ f n → n + f n)


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
sym {A} {x} {y} = transport (λ z → z ≡ x) refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {A} {x} {y} {z} = transport (λ w → w ≡ z → x ≡ z) (λ q → q)

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f {x} {y} = transport (λ z → f x ≡ f z) refl


--------
-- Peano axioms

suc-functional : {x y : ℕ} → x ≡ y → suc x ≡ suc y
suc-functional = cong (λ z → suc z)

suc-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-injective = cong pred

data ⊤ : Set where
  unit : ⊤

data ⊥ : Set where

zero-suc-disjoint : (x : ℕ) → suc x ≡ zero → ⊥
zero-suc-disjoint x = transport (ind₁ (λ _ → Set) ⊥ (λ _ _ → ⊤)) unit

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

-- an alternative proof of 1 + 1 ≡ 2 purely using the Peano axioms (instead of invoking computation)

1+1≡2' : suc zero + suc zero ≡ suc (suc zero)
1+1≡2' = trans (add-second-equation zero (suc zero)) (suc-functional (add-first-equation (suc zero)))


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
add-assoc zero    y z =
  (zero + y) + z
      ≡[ refl ]
  zero + (y + z) ∎
add-assoc (suc x) y z =
  ((suc x) + y) + z
      ≡[ refl ]
  (suc (x + y)) + z
      ≡[ refl ]
  suc ((x + y) + z)
      ≡[ refl ]
  suc ((x + y) + z)
      ≡[ cong suc (add-assoc x y z) ]
  suc (x + (y + z))
      ≡[ refl ]
  (suc x) + (y + z) ∎

-- an alternative proof of associativity of addition which explicitly invokes the induction principle

add-assoc' : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
add-assoc' x y z = ind (λ w → (w + y) + z ≡ w + (y + z)) base-case ind-case x
  where
    base-case : (zero + y) + z ≡ zero + (y + z)
    base-case =  (zero + y) + z
                     ≡[ refl ]
                 zero + (y + z) ∎
    ind-case : (w : ℕ) → (w + y) + z ≡ w + (y + z) → ((suc w) + y) + z ≡ suc w + (y + z)
    ind-case w ih =  ((suc w) + y) + z
                         ≡[ refl ]
                     (suc (w + y)) + z
                         ≡[ refl ]
                     suc ((w + y) + z)
                         ≡[ refl ]
                     suc ((w + y) + z)
                         ≡[ cong suc ih ]
                     suc (w + (y + z))
                         ≡[ refl ]
                     (suc w) + (y + z) ∎

-- addition is commutative

add-zero : (y : ℕ) → y ≡ y + zero
add-zero zero    =
  zero
      ≡[ refl ]
  zero + zero ∎
add-zero (suc y) =
  suc y
      ≡[ cong suc (add-zero y) ]
  suc (y + zero)
      ≡[ refl ]
  (suc y) + zero ∎

add-suc : (y x : ℕ) → suc (y + x) ≡ y + suc x
add-suc zero    x =
  suc (zero + x)
      ≡[ refl ]
  suc x
      ≡[ refl ]
  zero + suc x ∎
add-suc (suc y) x =
  suc ((suc y) + x)
      ≡[ refl ]
  suc (suc (y + x))
      ≡[ cong suc (add-suc y x) ]
  suc (y + suc x)
      ≡[ refl ]
  (suc y) + suc x
      ≡[ refl ]
  (suc y) + suc x ∎

add-comm : (x y : ℕ) → x + y ≡ y + x
add-comm zero    y =
  zero + y
      ≡[ refl ]
  y
      ≡[ add-zero y ]
  y + zero ∎
add-comm (suc x) y =
  (suc x) + y
      ≡[ refl ]
  suc (x + y)
      ≡[ cong suc (add-comm x y) ]
  suc (y + x)
      ≡[ add-suc y x ]
  y + suc x ∎

-- multiplication left-distributes over addition

left-distr : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
left-distr zero    y z =
  zero * (y + z)
      ≡[ refl ]
  zero
      ≡[ refl ]
  zero + zero
      ≡[ refl ]
  zero * y + zero * z ∎
left-distr (suc x) y z =
  (suc x) * (y + z)
      ≡[ refl ]
  (y + z) + x * (y + z)
      ≡[ cong (λ w → (y + z) + w) (left-distr x y z) ]
  (y + z) + (x * y + x * z)
      ≡[ add-assoc y z (x * y + x * z) ]
  y + (z + (x * y + x * z))
      ≡[ cong (λ w → y + w) (sym (add-assoc z (x * y) (x * z))) ]
  y + ((z + x * y) + x * z)
      ≡[ cong (λ w → y + w + x * z) (add-comm z (x * y)) ]
  y + ((x * y + z) + x * z)
      ≡[ cong (λ w → y + w) (add-assoc (x * y) z (x * z)) ]
  y + (x * y + (z + x * z))
      ≡[ sym (add-assoc y (x * y) (z + x * z)) ]
  (y + x * y) + (z + x * z)
      ≡[ refl ]
  (suc x) * y + (suc x) * z ∎

-- multiplication is commutative

mult-zero : (y : ℕ) → zero ≡ y * zero
mult-zero zero    =
  zero
      ≡[ refl ]
  zero * zero ∎
mult-zero (suc y) =
  zero
      ≡[ mult-zero y ]
  y * zero
      ≡[ refl ]
  zero + y * zero
      ≡[ refl ]
  (suc y) * zero ∎

mult-one : (y : ℕ) → y ≡ y * suc zero
mult-one zero    =
  zero
      ≡[ refl ]
  zero * suc zero ∎
mult-one (suc y) =
  suc y
      ≡[ cong suc (mult-one y) ]
  suc (y * suc zero)
      ≡[ refl ]
  (suc zero) + y * suc zero
      ≡[ refl ]
  (suc y) * suc zero ∎

mult-comm : (x y : ℕ) → x * y ≡ y * x
mult-comm zero    y =
  zero * y
      ≡[ refl ]
  zero
      ≡[ mult-zero y ]  
  y * zero ∎
mult-comm (suc x) y =
  (suc x) * y
      ≡[ refl ]
  y + x * y
      ≡[ cong (λ z → y + z) (mult-comm x y) ]
  y + y * x
      ≡[ cong (λ z → z + y * x) (mult-one y) ]
  y * suc zero + y * x
      ≡[ sym (left-distr y (suc zero) x) ]
  y * (suc zero + x)
      ≡[ refl ]
  y * suc x ∎

-- multiplication right-distributes over addition

right-distr : (x y z : ℕ) → (x + y) * z ≡ x * z + y * z
right-distr x y z =
  (x + y) * z
    ≡[ mult-comm (x + y) z ]
  z * (x + y)
    ≡[ left-distr z x y ]
  z * x + z * y
    ≡[ cong (λ w → w + z * y) (mult-comm z x) ]
  x * z + z * y
    ≡[ cong (λ w → x * z + w) (mult-comm z y) ]
  x * z + y * z ∎

-- multiplication is associative

mult-assoc : (x y z : ℕ) → (x * y) * z ≡ x * (y * z)
mult-assoc zero    y z =
  (zero * y) * z
      ≡[ refl ]
  zero * z
      ≡[ refl ]
  zero
      ≡[ refl ]
  zero * (y * z) ∎
mult-assoc (suc x) y z =
  ((suc x) * y) * z
      ≡[ refl ]
  (y + x * y) * z
      ≡[ right-distr y (x * y) z ]
  y * z + (x * y) * z
      ≡[ cong (λ w → y * z + w) (mult-assoc x y z) ]
  y * z + x * (y * z)
      ≡[ refl ]
  (suc x) * (y * z) ∎
