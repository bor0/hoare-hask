module Common where

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

data Pos = GoLeft | GoRight deriving (Eq)

type Path = [Pos]

-- Don't use this constructor directly. You should only construct proofs given the rules.
newtype Proof a = Proof a deriving (Eq)

fromProof :: Proof a -> a
fromProof (Proof a) = a

instance Show a => Show (Proof a) where
  show (Proof a) = "|- " ++ show a
