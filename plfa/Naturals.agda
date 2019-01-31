module plfa.Naturals where


data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- writing proofs in agda using Reasoning:

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩ -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩ -- induction
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩
    5
  ∎

-- far shorter proof
_ : 2 + 5 ≡ 7
_ = refl

-- multiplication
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)


-- exponentiation
_^_ : ℕ → ℕ → ℕ
n ^ 0 = 1
n ^ suc m = n * (n ^ m)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_∘_ : ℕ → ℕ → ℕ
zero ∘ n = n
suc m ∘ n = suc (n + m)


