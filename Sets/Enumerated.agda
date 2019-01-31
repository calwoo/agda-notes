module Sets.Enumerated where

-- Agda is a PL based on Martin-Lof intuitionistic type
-- theory. Here, types and values are effectively blended
-- together.

-- We can define types by the data construction. Here, the
-- symbol ": Set" means that Bool is a Set.

data Bool : Set where
  true : Bool
  false : Bool

-- Exercise 1: Define a set named Answer with three elements
-- → yes, no, maybe
data Answer : Set where
  yes : Answer
  no : Answer
  maybe : Answer

-- Exercise 2: Define a set named Quarter with four elements
-- → east, west, north and south.
data Quarter : Set where
  east : Quarter
  west : Quarter
  north : Quarter
  south : Quarter

-- Bool is a possible representation of the idea of a boolean.
-- Another representation may be

data Bool′ : Set where
  true′ : Bool′
  false′ : Bool′


-- This is isomorphic to Bool. We will deal with this later.
-- Now for some finite sets.

-- → Empty (or Void) has no constructor, as its the emptyset.

data Void : Set where

-- → Singleton (or One) has a single element (given by true).

data One : Set where
  tt : One

-- Philosophically, types and sets are different. A type is not
-- the collection of its elements. Calling data defines a type,
-- not a set.

-- Note that even though we call it Set, it should really mean
-- Type, the type of all types.

