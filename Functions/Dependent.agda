module Functions.Dependent where

open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s; _<_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)


-- A dependently typed function is of the form
  -- f : (x : A) → B, where B may depend on x.

-- ex)

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ zero = zero
fromℕ (suc n) = suc (fromℕ n)

-- These are ∏-types and as can be written in the type-theory literature
-- as ∏(x∈A)B.

-- Exercises 1: Define the following functions:

_-_ : (n : ℕ) → Fin (suc n) → ℕ
0 - _ = 0
(suc n) - zero = suc n
(suc n) - (suc m) = n - m

toℕ : ∀ {n} → Fin n → ℕ
toℕ zero = 0
toℕ (suc x) = suc (toℕ x)

-- Exercises 2: Define the functions for vector.

head : ∀ {n}{A : Set} → Vec A (suc n) → A
head (x ∷ xs) = x

tail : ∀ {n}{A : Set} → Vec A (suc n) → Vec A n
tail (x ∷ xs) = xs

_++_ : ∀ {n m}{A : Set} → Vec A n → Vec A m → Vec A (n + m)
[] ++ y = y
(x ∷ xs) ++ y = x ∷ (xs ++ y)

maps : ∀ {n}{A B : Set} → Vec (A → B) n → Vec A n → Vec B n
maps [] _ = []
maps (f ∷ fs) (a ∷ as) = (f a) ∷ (maps fs as)

replicate : ∀ {n}{A : Set} → A → Vec A n
replicate {zero} _ = []
replicate {suc n} a = a ∷ (replicate {n} a)

map : ∀ {n}{A B : Set} → (A → B) → Vec A n → Vec B n
map f x = maps (replicate f) x

-- zip : ∀ {n}{A B : Set} → Vec A n → Vec B n → Vec (A × B) n

-- Safe element indexing:
_!_ : ∀ {n}{A : Set} → Vec A n → Fin n → A
(a ∷ as) ! zero = a
(a ∷ as) ! (suc n) = as ! n


