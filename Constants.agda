module Constants where

open import Sets.Enumerated using (Bool; true; false)
open import Sets.Recursive using (ℕ; zero; suc)

-- To define constants in Agda, we need to name them, and then give
-- a proof/construction.

-- ex.

five : ℕ
five = suc (suc (suc (suc (suc zero))))

-- We can use constants in other definitions.

six : ℕ
six = suc five

-- Note that the type signatures here are optional, since we know
-- where they will land.

seven = suc six

-- If we type check this, the typechecker automatically knows it's in ℕ.

-- To get the normal form of an expression, use C-c C-n in agda-mode.
-- For example, six has normal form
-- -- suc (suc (suc (suc (suc (suc zero)))))


