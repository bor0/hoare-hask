module Common where

import PrettyPrinter

-- Helps when we want to avoid too many nested `whenRight`s
fromRight :: Either String p -> p
fromRight (Right x) = x
fromRight (Left x) = error x

whenRight :: Either a t -> (t -> Either a b) -> Either a b
whenRight (Right x) f = f x
whenRight (Left x)  _ = Left x

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

instance Pretty a => Pretty (Proof a) where
  prPrec x (Proof a) = "|- " ++ prPrec x a
