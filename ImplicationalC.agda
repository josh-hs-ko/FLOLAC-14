module ImplicationalC where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using () renaming (_≅_ to _≃_; refl to hrefl; trans to htrans; ≡-to-≅ to ≡-to-≃)
open import Function using (_∋_; _∘_; id)


--------
-- prelude

postulate String : Set

{-# BUILTIN STRING String #-}

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

-- data _≡_ {A : Set} (x : A) : A → Set where
--   refl : x ≡ x


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

infixl 5 _·_

data Term : ℕ → Set where  -- indexed with the number of free variables
  var : {n : ℕ} → Fin n           → Term n
  ƛ   : {n : ℕ} → Term (suc n)    → Term n
  _·_ : {n : ℕ} → Term n → Term n → Term n

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
θ // ƛ t     = ƛ ((θ ∘ suc) // t)
θ // (s · t) = (θ // s) · (θ // t)

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

wkr : {m n : ℕ} → Ren m n → Ren (suc m) (suc n)
wkr r zero    = zero
wkr r (suc i) = suc (r i)

ren : {m n : ℕ} → Ren m n → Shub m n
ren r zero    = var ∘ r
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

forgetⁱ : {p : PROP} {Γ : Cxt} → p ∈ Γ → Fin (length Γ)
forgetⁱ zero    = zero
forgetⁱ (suc i) = suc (forgetⁱ i)

forgetᵈ : {Γ : Cxt} {p : PROP} → Γ ⊢ p → Term (length Γ)
forgetᵈ (assum i) = var (forgetⁱ i)
forgetᵈ (⇒I d)   = ƛ (forgetᵈ d)
forgetᵈ (⇒E d e) = forgetᵈ d · forgetᵈ e

open import Relation.Binary.PropositionalEquality

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

-- inverse properties

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
  cong₂ app (forgetᵈ-well-typed-logicise-inverse (forgetᵈ d') d d' (fst (decong-⇒E eq)) refl)
            (forgetᵈ-well-typed-logicise-inverse (forgetᵈ e') e e' (snd (decong-⇒E eq)) refl)

lookup-within-range-forgetⁱ-inverse : {p : PROP} {Γ : Cxt} (i : p ∈ Γ) → lookup-within-range Γ (forgetⁱ i) (forgetⁱ-lookup i) ≡ i
lookup-within-range-forgetⁱ-inverse zero    = refl
lookup-within-range-forgetⁱ-inverse (suc i) = cong suc (lookup-within-range-forgetⁱ-inverse i)

logicise-forgetᵈ-inverse : {Γ : Cxt} {p : PROP} → (d : Γ ⊢ p) → logicise (forgetᵈ d) (forgetᵈ-well-typed d refl) ≡ d
logicise-forgetᵈ-inverse (assum i) = cong assum (lookup-within-range-forgetⁱ-inverse i)
logicise-forgetᵈ-inverse (⇒I d)   = cong ⇒I (logicise-forgetᵈ-inverse d)
logicise-forgetᵈ-inverse (⇒E d e) = cong₂ ⇒E (logicise-forgetᵈ-inverse d) (logicise-forgetᵈ-inverse e)

cong₂-pair : {A : Set} {B : A → Set} {a a' : A} {b : B a} {b' : B a'} → a ≡ a' → b ≃ b' → (Σ A B ∋ a , b) ≡ (a' , b')
cong₂-pair refl hrefl = refl

cong-forgetᵈ-well-typed :
  {Γ : Cxt} {p : PROP} (d : Γ ⊢ p) {t t' : Term (length Γ)} (eq : t ≡ forgetᵈ d) (eq' : t' ≡ forgetᵈ d) →
  forgetᵈ-well-typed d eq ≃ forgetᵈ-well-typed d eq'
cong-forgetᵈ-well-typed d refl refl = hrefl

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
validity-exercise p q σ with ⟦ p ⟧ σ
validity-exercise p q σ | false = refl
validity-exercise p q σ | true  with ⟦ q ⟧ σ
validity-exercise p q σ | true  | false = refl
validity-exercise p q σ | true  | true  = refl

validity-implies-semantic-consequence : (p : PROP) → Valid p → [] ⊧ p
validity-implies-semantic-consequence p v σ σ⊧[] = v σ

semantic-consequence-implies-validity : (p : PROP) → [] ⊧ p → Valid p
semantic-consequence-implies-validity p ⊧p σ = ⊧p σ nil

-- soundness

data Eq (p : PROP) (σ : Assignment) (b : Bool) : Set where
  E : ⟦ p ⟧ σ ≡ b → Eq p σ b

equation : (p : PROP) (σ : Assignment) → Eq p σ (⟦ p ⟧ σ)
equation p σ = E refl

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
