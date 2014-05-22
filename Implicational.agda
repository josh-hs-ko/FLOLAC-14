module Implicational (V : Set) where

open import Data.Empty
open import Data.Product
open import Data.Nat
open import Data.List
open import Data.Fin
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using () renaming (_≅_ to _≃_; refl to hrefl; trans to htrans; ≡-to-≅ to ≡-to-≃)


--------
-- propositional logic and natural deduction

infixr 5 _⇒_

data PROP : Set where
  var : V           → PROP
  _⇒_ : PROP → PROP → PROP

infix 2 _∈_

data _∈_ {A : Set} : A → List A → Set where
  zero : {x   : A} {xs : List A}          → x ∈ x ∷ xs
  suc  : {x y : A} {xs : List A} → x ∈ xs → x ∈ y ∷ xs

infix 2 _⊢_

Cxt : Set
Cxt = List PROP

data _⊢_ : Cxt → PROP → Set where

  assum : {Γ : Cxt} {p : PROP} →

            p ∈ Γ    →
          ----------
            Γ ⊢ p

  ⇒I : {Γ : Cxt} {p q : PROP} →

          p ∷ Γ ⊢ q   →
        -------------
          Γ ⊢ p ⇒ q

  ⇒E : {Γ : Cxt} {p q : PROP} →

          Γ ⊢ p ⇒ q    →    Γ ⊢ p    →
        ---------------------------- 
                   Γ ⊢ q

-- consistency : ¬ ((p : PROP) → [] ⊢ p)


--------
-- simply typed λ-calculus à la Curry

data Term : ℕ → Set where
  var : {n : ℕ} → Fin n → Term n
  ƛ   : {n : ℕ} → Term (suc n) → Term n
  _·_ : {n : ℕ} → Term n → Term n → Term n

lookup : (Γ : Cxt) → Fin (length Γ) → PROP
lookup []      ()
lookup (p ∷ Γ) zero    = p
lookup (p ∷ Γ) (suc i) = lookup Γ i

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

infix 1 _≅_

record _≅_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    to-from-inverse : (y : B) → to (from y) ≡ y
    from-to-inverse : (x : A) → from (to x) ≡ x

forgetⁱ : {p : PROP} {Γ : Cxt} → p ∈ Γ → Fin (length Γ)
forgetⁱ zero    = zero
forgetⁱ (suc i) = suc (forgetⁱ i)

forgetᵈ : {Γ : Cxt} {p : PROP} → Γ ⊢ p → Term (length Γ)
forgetᵈ (assum i) = var (forgetⁱ i)
forgetᵈ (⇒I d)   = ƛ (forgetᵈ d)
forgetᵈ (⇒E d e) = forgetᵈ d · forgetᵈ e

forgetⁱ-lookup : {p : PROP} {Γ : Cxt} → (i : p ∈ Γ) → p ≡ lookup Γ (forgetⁱ i)
forgetⁱ-lookup zero    = refl
forgetⁱ-lookup (suc i) = forgetⁱ-lookup i

forgetᵈ-well-typed : {Γ : Cxt} {p : PROP} (d : Γ ⊢ p) {t : Term (length Γ)} → t ≡ forgetᵈ d → Γ ⊢ t ∶ p
forgetᵈ-well-typed (assum i) refl = var (forgetⁱ-lookup i)
forgetᵈ-well-typed (⇒I d)   refl = abs (forgetᵈ-well-typed d refl)
forgetᵈ-well-typed (⇒E d e) refl = app (forgetᵈ-well-typed d refl) (forgetᵈ-well-typed e refl)

lookup-within-range : (Γ : Cxt) (i : Fin (length Γ)) {p : PROP} → p ≡ lookup Γ i → p ∈ Γ
lookup-within-range []      ()      eq
lookup-within-range (p ∷ Γ) zero    refl = zero
lookup-within-range (p ∷ Γ) (suc i) eq   = suc (lookup-within-range Γ i eq)

logicise : {Γ : Cxt} {p : PROP} → (t : Term (length Γ)) → Γ ⊢ t ∶ p → Γ ⊢ p
logicise .(var i) (var {Γ} {i} eq)      = assum (lookup-within-range Γ i eq)
logicise .(ƛ t)   (abs {Γ} {t} d)       = ⇒I (logicise t d)
logicise .(t · u) (app {Γ} {t} {u} d e) = ⇒E (logicise t d) (logicise u e)

forgetⁱ-lookup-within-range-inverse : (Γ : Cxt) (i : Fin (length Γ)) {p : PROP} (eq : p ≡ lookup Γ i) → forgetⁱ (lookup-within-range Γ i eq) ≡ i
forgetⁱ-lookup-within-range-inverse []      ()      eq
forgetⁱ-lookup-within-range-inverse (x ∷ Γ) zero    refl = refl
forgetⁱ-lookup-within-range-inverse (x ∷ Γ) (suc i) eq   = cong suc (forgetⁱ-lookup-within-range-inverse Γ i eq)

forgetᵈ-logicise-inverse : {Γ : Cxt} {p : PROP} → (t : Term (length Γ)) (d : Γ ⊢ t ∶ p) → forgetᵈ (logicise t d) ≡ t
forgetᵈ-logicise-inverse .(var i) (var {Γ} {i} eq)      = cong var (forgetⁱ-lookup-within-range-inverse Γ i eq)
forgetᵈ-logicise-inverse .(ƛ t)   (abs {Γ} {t} d)       = cong ƛ (forgetᵈ-logicise-inverse t d)
forgetᵈ-logicise-inverse .(t · u) (app {Γ} {t} {u} d e) = cong₂ _·_ (forgetᵈ-logicise-inverse t d) (forgetᵈ-logicise-inverse u e)

decong-⇒I : {Γ : Cxt} {p q : PROP} {d e : q ∷ Γ ⊢ p} → ⇒I d ≡ ⇒I e → d ≡ e
decong-⇒I refl = refl

domain-match : {Γ : Cxt} {p q p' : PROP} {d : Γ ⊢ p ⇒ q} {e : Γ ⊢ p} {d' : Γ ⊢ p' ⇒ q} {e' : Γ ⊢ p'} → ⇒E d e ≡ ⇒E d' e' → p ≡ p'
domain-match refl = refl

decong-⇒E : {Γ : Cxt} {p q : PROP} {d d' : Γ ⊢ p ⇒ q} {e e' : Γ ⊢ p} → ⇒E d e ≡ ⇒E d' e' → d ≡ d' × e ≡ e'
decong-⇒E refl = refl , refl

forgetᵈ-well-typed-logicise-inverse :
  {Γ : Cxt} {p : PROP} (t : Term (length Γ)) (d : Γ ⊢ t ∶ p) (d' : Γ ⊢ p) → d' ≡ logicise t d → (eq' : t ≡ forgetᵈ d') →
  forgetᵈ-well-typed d' eq' ≡ d
forgetᵈ-well-typed-logicise-inverse .(var (forgetⁱ i))         (var {Γ} eq'')        (assum i)   eq refl =
  cong var (proof-irrelevance (forgetⁱ-lookup i) eq'')
forgetᵈ-well-typed-logicise-inverse .(var i)                   (var {Γ} {i} eq'')    (⇒I d')     () eq'
forgetᵈ-well-typed-logicise-inverse .(var i)                   (var {Γ} {i} eq'')    (⇒E d' e')  () eq'
forgetᵈ-well-typed-logicise-inverse .(ƛ t)                     (abs {Γ} {t} d)       (assum x)   () eq'
forgetᵈ-well-typed-logicise-inverse .(ƛ (forgetᵈ d'))          (abs d)               (⇒I d')     eq refl =
  cong abs (forgetᵈ-well-typed-logicise-inverse (forgetᵈ d') d d' (decong-⇒I eq) refl)
forgetᵈ-well-typed-logicise-inverse .(ƛ t)                     (abs {Γ} {t} d)       (⇒E d' d'') () eq'
forgetᵈ-well-typed-logicise-inverse .(t · u)                   (app {Γ} {t} {u} d e) (assum i)    () eq'
forgetᵈ-well-typed-logicise-inverse .(t · u)                   (app {Γ} {t} {u} d e) (⇒I d')     () eq'
forgetᵈ-well-typed-logicise-inverse .(forgetᵈ d' · forgetᵈ e') (app d e)             (⇒E d' e')  eq refl with domain-match eq
forgetᵈ-well-typed-logicise-inverse .(forgetᵈ d' · forgetᵈ e') (app d e)             (⇒E d' e')  eq refl | refl =
  cong₂ app (forgetᵈ-well-typed-logicise-inverse (forgetᵈ d') d d' (proj₁ (decong-⇒E eq)) refl)
            (forgetᵈ-well-typed-logicise-inverse (forgetᵈ e') e e' (proj₂ (decong-⇒E eq)) refl)

lookup-within-range-forgetⁱ-inverse : {p : PROP} {Γ : Cxt} (i : p ∈ Γ) → lookup-within-range Γ (forgetⁱ i) (forgetⁱ-lookup i) ≡ i
lookup-within-range-forgetⁱ-inverse zero    = refl
lookup-within-range-forgetⁱ-inverse (suc i) = cong suc (lookup-within-range-forgetⁱ-inverse i)

logicise-forgetᵈ-inverse : {Γ : Cxt} {p : PROP} → (d : Γ ⊢ p) → logicise (forgetᵈ d) (forgetᵈ-well-typed d refl) ≡ d
logicise-forgetᵈ-inverse (assum i) = cong assum (lookup-within-range-forgetⁱ-inverse i)
logicise-forgetᵈ-inverse (⇒I d)   = cong ⇒I (logicise-forgetᵈ-inverse d)
logicise-forgetᵈ-inverse (⇒E d e) = cong₂ ⇒E (logicise-forgetᵈ-inverse d) (logicise-forgetᵈ-inverse e)

cong₂-pair : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'} → a ≡ a' → b ≃ b' → _≡_ {_} {Σ A B} (a , b) (a' , b')
cong₂-pair refl hrefl = refl

cong-forgetᵈ-well-typed :
  {Γ : Cxt} {p : PROP} (d : Γ ⊢ p) {t t' : Term (length Γ)} (eq : t ≡ forgetᵈ d) (eq' : t' ≡ forgetᵈ d) →
  forgetᵈ-well-typed d eq ≃ forgetᵈ-well-typed d eq'
cong-forgetᵈ-well-typed d refl refl = hrefl

Curry-Howard : (Γ : Cxt) (p : PROP) →  Γ ⊢ p  ≅  (Σ[ t ∶ Term (length Γ) ] Γ ⊢ t ∶ p)
Curry-Howard Γ p = record
  { to   = λ d → forgetᵈ d , forgetᵈ-well-typed d refl
  ; from = uncurry logicise
  ; to-from-inverse = λ { (t , d) → cong₂-pair (forgetᵈ-logicise-inverse t d)
                                               (htrans (cong-forgetᵈ-well-typed
                                                          (logicise t d) refl (sym (forgetᵈ-logicise-inverse t d)))
                                                       (≡-to-≃ (forgetᵈ-well-typed-logicise-inverse t d (logicise t d) refl
                                                                  (sym (forgetᵈ-logicise-inverse t d))))) }
  ; from-to-inverse = logicise-forgetᵈ-inverse }


--------
-- two-valued semantics

data Bool : Set where
  false : Bool
  true  : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if false then x else y = x
if true  then x else y = y

Assignment : Set
Assignment = V → Bool

⟦_⟧ : PROP → Assignment → Bool
⟦ var x ⟧ σ = σ x
⟦ p ⇒ q ⟧ σ = if ⟦ p ⟧ σ then true else ⟦ q ⟧ σ

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
validity-exercise p q σ with ⟦ p ⟧ σ 
validity-exercise p q σ | false = refl
validity-exercise p q σ | true with ⟦ q ⟧ σ 
validity-exercise p q σ | true | false = refl
validity-exercise p q σ | true | true  = refl

validity-semantic-consequence : (p : PROP) → Valid p → [] ⊧ p
validity-semantic-consequence p v σ σ⊧[] = v σ

semantic-consequence-validity : (p : PROP) → [] ⊧ p → Valid p
semantic-consequence-validity p ⊧p σ = ⊧p σ nil

-- soundness

data Magic (p : PROP) (σ : Assignment) : Bool → Set where
  E : {b : Bool} → ⟦ p ⟧ σ ≡ b → Magic p σ b

magic : (p : PROP) (σ : Assignment) (b : Bool) → ⟦ p ⟧ σ ≡ b → Magic p σ b
magic p σ false eq = E eq
magic p σ true  eq = E eq

equation : (p : PROP) (σ : Assignment) → Magic p σ (⟦ p ⟧ σ)
equation p σ = magic p σ (⟦ p ⟧ σ) refl

impossible : {b : Bool} → b ≡ true → b ≡ false → {A : Set} → A
impossible refl ()

infix 5 _!!_

_!!_ : {σ : Assignment} {p : PROP} {Γ : Cxt} → σ Models Γ → p ∈ Γ → σ models p
cons m ms !! zero  = m
cons m ms !! suc i = ms !! i

soundness : {Γ : Cxt} {p : PROP} → Γ ⊢ p → Γ ⊧ p
soundness (assum i           ) σ σ⊧Γ = σ⊧Γ !! i
soundness (⇒I {Γ} {p} t      ) σ σ⊧Γ with ⟦ p ⟧ σ | equation p σ
soundness (⇒I {Γ} {p} t      ) σ σ⊧Γ | false | E σ/⊧⟦p⟧σ = refl
soundness (⇒I {Γ} {p} t      ) σ σ⊧Γ | true  | E σ⊧⟦p⟧σ  = soundness t σ (cons σ⊧⟦p⟧σ σ⊧Γ)
soundness (⇒E {Γ} {p} {q} s t) σ σ⊧Γ with soundness s σ σ⊧Γ
soundness (⇒E {Γ} {p} {q} s t) σ σ⊧Γ | σ⊧q with ⟦ p ⟧ σ | equation p σ
soundness (⇒E {Γ} {p} {q} s t) σ σ⊧Γ | σ⊧q | false | E σ/⊧⟦p⟧σ = impossible (soundness t σ σ⊧Γ) σ/⊧⟦p⟧σ
soundness (⇒E {Γ} {p} {q} s t) σ σ⊧Γ | σ⊧q | true  | E σ⊧⟦p⟧σ  = σ⊧q

-- completeness : {Γ : Cxt} {p : PROP} → Γ ⊧ p → Γ ⊢ p
