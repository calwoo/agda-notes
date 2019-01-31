module Functions.Cases where

open import Sets.Enumerated using (Bool; true; false)

-- Functions can be defined in Agda like they are in Haskell.
-- As a basic construct, we use pattern matching.

not : Bool → Bool
not true = false
not false = true

-- Functions are not relations, they are computational. They come with
-- an algorithm for how to compute a value.

-- Logical AND

_∧_ : Bool → Bool → Bool
true  ∧ x = x
false ∧ _ = false

infixr 6 _∧_

-- Exercise 1: Give logical OR.

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ x = x

infixr 5 _∨_

-- Exercise 2: Define logical OR with not and _∧_.

_∨′_ : Bool → Bool → Bool
x ∨′ y = not (not x ∧ not y)


