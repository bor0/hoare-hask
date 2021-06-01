module Common where

import PrettyPrinter

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

instance (Show a, Pretty b) => Pretty (Either a b) where
  prPrec x (Right a) = prPrec x a
  prPrec x (Left a)  = show a

instance Pretty a => Pretty (Proof a) where
  prPrec x (Proof a) = "|- " ++ prPrec x a
