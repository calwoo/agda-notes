module peano where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- mixfix plus operator given by induction
_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + n = n
(suc n) + n′ = suc (n + n′)




