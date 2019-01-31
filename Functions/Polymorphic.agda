module Functions.Polymorphic where

open import Data.Nat
open import Data.Unit using (⊤; tt)

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A

infixr 5 _::_

-- Concatenation

_++_ : {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- This is a polymorphic function. The curly braces {} means that the
-- typevar is implicit. If we used (), then we'd have to explicitly
-- declare the typevar each time we call the function.
-- In Agda, polymorphic parameters are explicit, unlike Haskell.

-- Exercise 1: Define an isomorphism between List ⊤ and ℕ!

fromList : List ⊤ → ℕ
fromList []      = 0
fromList (x :: xs) = suc (fromList xs)

toList : ℕ → List ⊤
toList 0       = []
toList (suc n) = tt :: (toList n)

-- Exercise 2: Define the following on lists:

map : {A B : Set} → (A → B) → List A → List B
map _ []        = []
map f (x :: xs) = (f x) :: (map f xs)

maps : {A B : Set} → List (A → B) → List A → List B
maps _ [] = []
maps (f :: fs) (x :: xs) = (f x) :: (maps fs xs)
maps _ _ = []

-- Exercise 3: Define the singleton list function.

[_] : {A : Set} → A → List A
[_] a = a :: []

-- Polymorphic id function.

id : {A : Set} → A → A
id a = a

-- We can specify implicit parameters manually using curly braces.

aNumber = id {ℕ} (suc zero)

-- Exercise 4: Define the following:

const : {A B : Set} → A → B → A
const a _ = a

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b


-- Some fun categorical objects.

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

-- Exercise 5: Define a function which swaps the two elements.

swap : {A B : Set} → A × B → B × A
swap (a , b) = b , a

-- Exercise 6: Define projection maps.

proj₁ : {A B : Set} → A × B → A
proj₁ (a , _) = a

proj₂ : {A B : Set} → A × B → B
proj₂ (_ , b) = b




data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- Exercise 7: Define a function that swaps the elements.

swap′ : {A B : Set} → A ⊎ B → B ⊎ A
swap′ (inj₁ a) = inj₂ a
swap′ (inj₂ b) = inj₁ b

-- Exercise 8: Define the eliminator function for disjoint union.

[_,_] : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
[_,_] f _ (inj₁ a) = f a
[_,_] _ g (inj₂ b) = g b



