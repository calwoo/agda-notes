-- Note on mutual recursive sets

module Sets.Mutual where

open import Sets.Enumerated using (Bool; true; false)
open import Syntax.Decimals using (ℕ; zero; suc)

-- To allow mutual definitions one should declare a set before using it.

data A : Set
data B : Set

data A where
  nil  : A
  _::_ : ℕ → B → A

data B where
  _::_ : Bool → A → B

-- Elements of these look like alternating lists of booleans and ℕ
-- terminating at a nil-element.

-- Q: Where is:

what : A
what = 3 :: (false :: (4 :: (true :: nil)))

-- Interestingly, dropping the type annotation here confuses the
-- typechecker.

-- Exercise: Define trees with nodes with finite children (0, 1, 2,...)

data Tree : Set
data NodeList : Set

data Tree where
  leaf : Tree
  node : NodeList → Tree

data NodeList where
  end : NodeList
  _::_ : Tree → NodeList → NodeList
