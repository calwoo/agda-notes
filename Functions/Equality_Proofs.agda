module Functions.Equality_Proofs where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Function using (_$_)

-- The definition of propositional equality:

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

-- _≡_ is an equivalence relation.

refl' : ∀ {A} (a : A) → a ≡ a
refl' a = refl

sym : ∀ {A} {a b : A} → a ≡ b → b ≡ a
sym refl = refl

-- Exercise 1:

trans : ∀ {A} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- Exercise 2: Prove every function is compatible with equivalence rel.
-- (congruency)

cong : ∀ {A B} {m n : A} → (f : A → B) → m ≡ n → f m ≡ f n
cong f refl = refl

-- Note that Agda reduces types automatically during type checking. This
-- is a safe operation since all functions terminate (otherwise they are
-- not defined!)

-- We say x and y are definitionally equal if and only if refl : x ≡ y.
-- It is the most trivial equality.


