module Sets.Recursive where
-- We can use import to grab definitions from other modules
open import Sets.Enumerated using (Bool; true; false)

-- Lets represent the peano natural numbers.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- to type check, using C-c C-d in agda-mode to deduce normal forms.

-- How about ℕ in binary?

data ℕ⁺ : Set where
  one      : ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero : ℕ₂
  id   : ℕ⁺ → ℕ₂

-- Exercise 1: How is 9 represented in ℕ₂?
-- -- As id (double+1 (double (double one))) : ℕ₂.

-- Exercise 2: Define ℤ.

data ℤ : Set where
  zero : ℤ
  id   : ℕ⁺ → ℤ
  neg  : ℕ⁺ → ℤ

-- Inductive definitions are pretty cool. We can represent other data
-- structures this way. For example, binary trees:

data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree

-- Exercise 3: Define binary trees with ℕ-data attached to leaves.

data BinℕTree : Set where
  leaf : ℕ → BinℕTree
  node : BinℕTree → BinℕTree → BinℕTree

-- Exercise 4: Define (finite) lists of natural numbers.

data FiniteList : Set where
  nil  : FiniteList
  cons : ℕ → FiniteList → FiniteList

-- Exercise 5: Define non-empty lists of ℕ.

data NonEmptyList : Set where
  last : ℕ → NonEmptyList
  cons : ℕ → NonEmptyList → NonEmptyList


