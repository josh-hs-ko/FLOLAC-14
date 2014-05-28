module Implicational where


--------
-- prelude

open import Data.String

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

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

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
if false then x else y = x
if true  then x else y = y

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
            Γ ⊢ p

  ⇒I : {Γ : Cxt} {p q : PROP} →

          p ∷ Γ ⊢ q   →
        --------------
          Γ ⊢ p ⇒ q

  ⇒E : {Γ : Cxt} {p q : PROP} →

          Γ ⊢ p ⇒ q    →    Γ ⊢ p    →
        ---------------------------- 
                   Γ ⊢ q

-- consistency : ¬ ((p : PROP) → [] ⊢ p)


--------
-- simply typed λ-calculus à la Curry

data Term : ℕ → Set where  -- indexed with the number of available bound variables
  var : {n : ℕ} → Fin n           → Term n
  ƛ   : {n : ℕ} → Term (suc n)    → Term n
  _·_ : {n : ℕ} → Term n → Term n → Term n

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

toTerm : {Γ : Cxt} {p : PROP} → Γ ⊢ p → Term (length Γ)
toTerm = {!!}

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
⟦ p ⇒ q  ⟧ σ = if ⟦ p ⟧ σ then true else ⟦ q ⟧ σ

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
validity-exercise = {!!}

validity-implies-semantic-consequence : (p : PROP) → Valid p → [] ⊧ p
validity-implies-semantic-consequence = {!!}

semantic-implies-consequence-validity : (p : PROP) → [] ⊧ p → Valid p
semantic-implies-consequence-validity = {!!}

-- soundness

data Eq (p : PROP) (σ : Assignment) (b : Bool) : Set where
  E : ⟦ p ⟧ σ ≡ b → Eq p σ b

equation : (p : PROP) (σ : Assignment) → Eq p σ (⟦ p ⟧ σ)
equation p σ = E refl

impossible : {b : Bool} → b ≡ true → b ≡ false → {A : Set} → A
impossible refl ()

soundness : {Γ : Cxt} {p : PROP} → Γ ⊢ p → Γ ⊧ p
soundness = {!!}

-- completeness : {Γ : Cxt} {p : PROP} → Γ ⊧ p → Γ ⊢ p
