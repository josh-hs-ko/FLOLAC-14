-- retrieved from Agda mailing list (I can't find the precise post, though..)

{-# OPTIONS --type-in-type #-}

module RussellC where

open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- a set is an indexed collection of elements, which are themselves sets
-- this declaration is rejected if the --type-in-type option is not given
data U : Set where
  set : (I : Set) → (I → U) → U

-- a set is regular exactly when it doesn't contain itself
Regular : U → Set
Regular (set I f) = (i : I) → f i ≢ set I f

-- Russell's set: the set of all regular sets
R : U
R = set (Σ U Regular) proj₁

-- R is not regular
R-nonreg : ¬ Regular R
R-nonreg reg = reg (R , reg) refl

-- R is regular
R-reg : Regular R
R-reg (x , reg) p = subst Regular p reg (x , reg) p

-- R cannot be regular and non-regular at the same time
contradiction : ⊥
contradiction = R-nonreg R-reg
