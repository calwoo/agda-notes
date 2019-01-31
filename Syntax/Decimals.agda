module Syntax.Decimals where


-- Peano ℕ expressions are hard to read with all that suc around.
-- How about regular (decimal) numbers?

-- A solution is to use the standard library definitions

open import Data.Nat public using (ℕ; zero; suc)
