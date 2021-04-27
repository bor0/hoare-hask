module Common where

-- Helps when we want to avoid too many nested `whenRight`s
rightProof :: Either String p -> p
rightProof (Right x) = x
rightProof (Left x) = error x

whenRight :: Either a t -> (t -> Either a b) -> Either a b
whenRight (Right x) f = f x
whenRight (Left x)  _ = Left x

whenLeft :: Either t b -> (t -> Either a b) -> Either a b
whenLeft (Left x) f   = f x
whenLeft (Right x)  _ = Right x

allSame :: Eq a => [a] -> Bool
allSame []  = False
allSame [x] = True
allSame xs  = all (== head xs) (tail xs)

{- Position data structure, for applyXRule -}
data Pos = GoLeft | GoRight deriving (Eq, Show)
type Path = [Pos]

{- Proof data structure -}
-- Don't use this constructor directly. You should only construct proofs given the rules.
newtype Proof a = Proof a deriving (Eq, Show)

fromProof :: Proof a -> a
fromProof (Proof a) = a

{- Example variables -}
data Vars = A | B | C | D deriving (Eq, Ord, Show)

{- Pretty printer -}
class Pretty a where
  pr :: a -> String

instance Pretty a => Pretty (Proof a) where
  pr (Proof a) = "|- " ++ pr a

instance Pretty Vars where
  pr = show
