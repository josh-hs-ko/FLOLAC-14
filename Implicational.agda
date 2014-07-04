module Implicational where


--------
-- prelude

postulate String : Set

{-# BUILTIN STRING String #-}

id : {A : Set} → A → A
id x = x

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ

syntax Σ A (λ x → b) = Σ[ x ∶ A ] b

_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

infixr 3 _×_

uncurry : {A C : Set} {B : A → Set} → ((x : A) → B x → C) → Σ A B → C
uncurry f (x , y) = f x y

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
-- for Agda < 2.4.0
-- {-# BUILTIN ZERO zero #-}
-- {-# BUILTIN SUC  suc  #-}

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

length : {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

infix 2 _∈_

data _∈_ {A : Set} : A → List A → Set where
  zero : {x   : A} {xs : List A}          → x ∈ x ∷ xs
  suc  : {x y : A} {xs : List A} → x ∈ xs → x ∈ y ∷ xs

lookup : {A : Set} (xs : List A) → Fin (length xs) → A
lookup []       ()
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

data Bool : Set where
  false : Bool
  true  : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if false then x else y = y
if true  then x else y = x

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x


--------
-- propositional logic and natural deduction

infixr 5 _⇒_

Var : Set
Var = String

data PROP : Set where
  atom : Var         → PROP
  _⇒_  : PROP → PROP → PROP

infix 2 _⊢_

Cxt : Set
Cxt = List PROP

data _⊢_ : Cxt → PROP → Set where

  assum : {Γ : Cxt} {p : PROP} →

            p ∈ Γ    →
          ---------
            Γ ⊢ p  -- ⊢ (turnstile): entails

  ⇒I : {Γ : Cxt} {p q : PROP} →

          p ∷ Γ ⊢ q   →
        --------------
          Γ ⊢ p ⇒ q

  ⇒E : {Γ : Cxt} {p q : PROP} →

          Γ ⊢ p ⇒ q    →    Γ ⊢ p    →
        ---------------------------- 
                   Γ ⊢ q

diag : [] ⊢ (atom "A" ⇒ atom "A" ⇒ atom "B") ⇒ atom "A" ⇒ atom "B"
diag = ⇒I (⇒I (⇒E (⇒E (assum (suc zero)) (assum zero)) (assum zero)))

-- consistency : ¬ ((p : PROP) → [] ⊢ p)


--------
-- simply typed λ-calculus à la Curry

infixl 5 _·_

data Term : ℕ → Set where  -- indexed with the number of free variables
  var : {n : ℕ} → Fin n           → Term n
  ƛ   : {n : ℕ} → Term (suc n)    → Term n
  _·_ : {n : ℕ} → Term n → Term n → Term n

k : Term 0
k = ƛ (ƛ (var (suc zero)))  -- λx. λy. x

-- detour: an evaluator
-- (ref: Conor McBride's Cambridge lectures)

Sub : ℕ → ℕ → Set
Sub m n = Fin m → Term n

_+'_ : ℕ → ℕ → ℕ
zero  +' n = n
suc m +' n = m +' suc n

Shub : ℕ → ℕ → Set
Shub m n = (k : ℕ) → Sub (k +' m) (k +' n)

_//_ : {m n : ℕ} (θ : Shub m n) → Term m → Term n
θ // var i   = θ zero i
θ // ƛ t     = ƛ ((λ k → θ (suc k)) // t)
θ // (s · t) = (θ // s) · (θ // t)

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

wkr : {m n : ℕ} → Ren m n → Ren (suc m) (suc n)
wkr r zero    = zero
wkr r (suc i) = suc (r i)

ren : {m n : ℕ} → Ren m n → Shub m n
ren r zero    = λ i → var (r i)
ren r (suc k) = ren (wkr r) k

wks : {m n : ℕ} → Sub m n → Sub (suc m) (suc n)
wks s zero    = var zero
wks s (suc i) = ren suc // s i

sub : {m n : ℕ} → Sub m n → Shub m n
sub s zero    = s
sub s (suc k) = sub (wks s) k

zsub : {n : ℕ} → Term n → Sub (suc n) n
zsub t zero    = t
zsub t (suc i) = var i

_∧_ : Bool → Bool → Bool
false ∧ b = false
true  ∧ b = b

normal : {n : ℕ} → Term n → Bool
normal (var i       ) = true
normal (ƛ t         ) = normal t
normal (var i    · t) = normal t
normal (ƛ s      · t) = false
normal ((s · s') · t) = normal (s · s') ∧ normal t

reduce : {n : ℕ} → Term n → Term n
reduce (var i       ) = var i
reduce (ƛ t         ) = ƛ (reduce t)
reduce (var i    · t) = var i · reduce t
reduce (ƛ s      · t) = sub (zsub t) // s
reduce ((s · s') · t) = if normal (s · s') then (s · s') · reduce t else reduce (s · s') · t

find-normal : ℕ → ℕ → {n : ℕ} → Term n → Term n × ℕ
find-normal zero    n t = t , n
find-normal (suc k) n t = if normal t then (t , n) else find-normal k (suc n) (reduce t)

run : {n : ℕ} → Term n → Term n × ℕ
run t = find-normal 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 0 t

iter : ℕ → {n : ℕ} → Term (suc (suc n))
iter zero    = var zero
iter (suc n) = var (suc zero) · iter n

church : ℕ → {n : ℕ} → Term n
church n = ƛ (ƛ (iter n))

plus : {n : ℕ} → Term n
plus = ƛ (ƛ (ƛ (ƛ (var (suc (suc (suc zero))) · var (suc zero) · (var (suc (suc zero)) · var (suc zero) · var zero)))))

mult : {n : ℕ} → Term n
mult = ƛ (ƛ (var (suc zero) · (plus · var zero) · church 0))

orned-iter : List ℕ → {n : ℕ} → Term (suc (suc n))
orned-iter []       = var zero
orned-iter (x ∷ xs) = var (suc zero) · church x · orned-iter xs

list : List ℕ → {n : ℕ} → Term n
list xs = ƛ (ƛ (orned-iter xs))

sum : {n : ℕ} → Term n
sum = ƛ (var zero · plus · church 0)

prod : {n : ℕ} → Term n
prod = ƛ (var zero · mult · church 1)

-- end of detour

infix 2 _⊢_∶_

data _⊢_∶_ : (Γ : Cxt) → Term (length Γ) → PROP → Set where

  var : {Γ : Cxt} {i : Fin (length Γ)} {p : PROP} →

          p ≡ lookup Γ i    →
        ------------------
          Γ ⊢ var i ∶ p

  abs : {Γ : Cxt} {t : Term (suc (length Γ))} {p q : PROP} →

           p ∷ Γ ⊢ t ∶ q      →
        --------------------
          Γ ⊢ ƛ t ∶ p ⇒ q

  app : {Γ : Cxt} {t u : Term (length Γ)} {p q : PROP} →

          Γ ⊢ t ∶ p ⇒ q    →    Γ ⊢ u ∶ p    →
        ------------------------------------
                   Γ ⊢ t · u ∶ q


--------
-- The Curry-Howard isomorphism

toFin : {Γ : Cxt} {p : PROP} → p ∈ Γ → Fin (length Γ)
toFin zero = zero
toFin (suc i) = suc (toFin i)

toTerm : {Γ : Cxt} {p : PROP} → Γ ⊢ p → Term (length Γ)
toTerm (assum x) = var (toFin x)
toTerm (⇒I d) = ƛ (toTerm d)
toTerm (⇒E d d₁) = toTerm d · toTerm d₁

toTyping : {Γ : Cxt} {p : PROP} (d : Γ ⊢ p) → Γ ⊢ toTerm d ∶ p
toTyping = {!!}

toNJ : {Γ : Cxt} {p : PROP} → (t : Term (length Γ)) → Γ ⊢ t ∶ p → Γ ⊢ p
toNJ = {!!}

-- the isomorphism

infix 1 _≅_

record _≅_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    to-from-inverse : (y : B) → to (from y) ≡ y
    from-to-inverse : (x : A) → from (to x) ≡ x

Curry-Howard : (Γ : Cxt) (p : PROP) →  Γ ⊢ p  ≅  (Σ[ t ∶ Term (length Γ) ] Γ ⊢ t ∶ p)
Curry-Howard Γ p = record
  { to   = λ d → toTerm d , toTyping d
  ; from = uncurry toNJ
  ; to-from-inverse = {!!}
  ; from-to-inverse = {!!} }


--------
-- two-valued semantics

Assignment : Set
Assignment = Var → Bool

⟦_⟧ : PROP → Assignment → Bool
⟦ atom x ⟧ σ = σ x
⟦ p ⇒ q  ⟧ σ = if ⟦ p ⟧ σ then ⟦ q ⟧ σ else true

infix 3 _models_

_models_ : Assignment → PROP → Set
σ models p = ⟦ p ⟧ σ ≡ true

Valid : PROP → Set
Valid p = (σ : Assignment) → σ models p

infix 2 _Models_

data _Models_ (σ : Assignment) : Cxt → Set where
  nil  : σ Models []
  cons : {p : PROP} {Γ : Cxt} → σ models p → σ Models Γ → σ Models (p ∷ Γ)

_⊧_ : Cxt → PROP → Set
Γ ⊧ p = (σ : Assignment) → σ Models Γ → σ models p

validity-exercise : (p q : PROP) → Valid ((p ⇒ (p ⇒ q)) ⇒ (p ⇒ q))
validity-exercise p q σ with ⟦ p ⟧ σ | ⟦ q ⟧ σ
validity-exercise p q σ | false | false = refl
validity-exercise p q σ | false | true  = refl
validity-exercise p q σ | true  | false = refl
validity-exercise p q σ | true  | true  = refl

validity-implies-semantic-consequence : (p : PROP) → Valid p → [] ⊧ p
validity-implies-semantic-consequence = {!!}

semantic-consequence-implies-validity : (p : PROP) → [] ⊧ p → Valid p
semantic-consequence-implies-validity = {!!}

-- soundness

data Eq (p : PROP) (σ : Assignment) (b : Bool) : Set where
  E : ⟦ p ⟧ σ ≡ b → Eq p σ b

equation : (p : PROP) (σ : Assignment) → Eq p σ (⟦ p ⟧ σ)
equation p σ = E refl

impossible : {b : Bool} → b ≡ true → b ≡ false → {A : Set} → A
impossible refl ()

soundness : {Γ : Cxt} {p : PROP} → Γ ⊢ p → Γ ⊧ p
soundness (assum x) σ x₁ = {!!}
soundness (⇒I d) σ x = {!!}
soundness (⇒E d d₁) σ x = {!!}

-- completeness : {Γ : Cxt} {p : PROP} → Γ ⊧ p → Γ ⊢ p
