module Sets.Parametric where
open import Data.Nat

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

infixr 5 _::_

-- Here, A is a typevar. This is an example of parametric polymorphism
-- in Agda.

-- Exercise 1: Define a Maybe set (lists with 0 or 1 elements)

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A


-- There are various operations to create types.
-- × Cartesian product

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

-- ⊎ Disjoint union

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- Exercise 2: Give an isomorphic definition of Maybe A.

data Truth : Set where
  tt : Truth

data Maybe′ (A : Set) : Set where
  maybe : A ⊎ Truth → Maybe′ A

-- Parametric polymorphism also works with mutual recursion.

data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B : Set) where
  []   : List₁ A B
  _::_ : A → List₂ A B → List₁ A B

data List₂ (A B : Set) where
  _::_ : B → List₁ A B → List₂ A B

