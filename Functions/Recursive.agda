module Functions.Recursive where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; zero)

-- Functions can be defined recursively.

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_

-- Exercise 1: Define the following.

pred : ℕ → ℕ
pred       0 = 0
pred (suc x) = x

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ -- subtraction
n ∸     0 = n
0 ∸ suc n = 0
(suc n) ∸ (suc m) = n ∸ m


-- Exercise 2: Define even and odd functions.

odd : ℕ → Bool
even : ℕ → Bool

odd 0 = false
odd (suc 0) = true
odd (suc x) = even x

even 0 = true
even (suc 0) = false
even (suc x) = odd x


