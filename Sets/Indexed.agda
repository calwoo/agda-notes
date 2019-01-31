module Sets.Indexed where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)

-- We want to define a ℕ-indexed family of sets Fin so
-- that Fin n has exactly n elements. This is the start of
-- dependent type theory, in which types have definitions
-- that depend on a value.

data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)

-- Lets unpack this. We think of n : ℕ as an "upper bound"
-- for elements in the finite set. So zero n is to be an
-- element of a finite set. Which one? Well it can't be in
-- Fin 0, it has no elements! So it fits in the successor.
-- Same with suc n. It then becomes a function that takes an
-- element of a finite set and pushes it up one-- but that
-- changes the lower bound. So it's one level higher.

-- Exercise 1: Define a bool-indexed family of sets so that
-- the set indexed by false contains no elements and the set
-- indexed by true contains one element.

data Indicator : Bool → Set where
  one : Indicator true

-- Exercise 2: Define a ℕ-indexed family of sets so that evens
-- have one element and the others are empty.

data Eveners : ℕ → Set where
  first : Eveners zero
  next : (n : ℕ) → Eveners n → Eveners (suc (suc n))

-- Next is the stereotypical dependent type: the vector.
-- A vector of type A is an n-tuple of elements of A.

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)

-- ex) [] : Vec ℕ 0
-- ex) cons 1 false (cons 0 true []) : Vec Bool 2

-- Exercise 3: Define a bool-indexed family of sets with two
-- parameters, A and B, such that the set indexed by false contains
-- an A element and the set indexed by true contains a B element.

data Either (A B : Set) : Bool → Set where
  left  : A → Either A B false
  right : B → Either A B true
