module Sets.Propositions where

open import Data.Nat using (ℕ; zero; suc)

-- The key mantra of type theory is that types are propositions and values are proofs.
-- For example, let us denote proofs of the true proposition by the type ⊤.

-- It has a trivial proof: tt : ⊤!

data ⊤ : Set where
  tt : ⊤

-- Proofs of the false proposition has type ⊥. Since there are no such proofs of a
-- false statement, we give no constructors.

data ⊥ : Set where

-- Proofs of the conjunction of two propositions A, B have type A × B.
-- It has proofs of the form a, b where a : A and b : B.

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

-- Proofs of the disjunction of two propositions A, B have type A ⊎ B.
-- It has two types of proofs:
   -- inj₁ a where a : A
   -- inj₂ b where b : B

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- Exercise 1: Construct a proof for the following propositions.
-- ⊤ × ⊤
⊤×⊤ : ⊤ × ⊤
⊤×⊤ = tt , tt
-- ⊤ × ⊥ has none
-- ⊥ × ⊥ has none
-- ⊤ ⊎ ⊤
first⊤ : ⊤ ⊎ ⊤
first⊤ = inj₁ tt


data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m : ℕ} → {n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

-- In particular, we get proofs like
-- s≤s (s≤s (z≤n {3})) : 2 ≤ 5

