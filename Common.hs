module Common where

whenRight :: Either a t -> (t -> Either a b) -> Either a b
whenRight (Right x) f = f x
whenRight (Left x)  _ = Left x

whenLeft :: Either t b -> (t -> Either a b) -> Either a b
whenLeft (Left x) f   = f x
whenLeft (Right x)  _ = Right x

allSame :: Eq a => [a] -> Bool
allSame xs = all (== head xs) (tail xs)

data Pos = GoLeft | GoRight deriving (Eq)

type Path = [Pos]

-- Don't use this constructor directly. You should only construct proofs given the rules.
newtype Proof a = Proof a deriving (Eq)

fromProof :: Proof a -> a
fromProof (Proof a) = a

data Arith a =
  Var a
  | Z
  | S (Arith a)
  | Plus (Arith a) (Arith a)
  | Mult (Arith a) (Arith a)
  deriving (Eq)

data PropCalc a =
  PropVar a
  | Not (PropCalc a)
  | And (PropCalc a) (PropCalc a)
  | Or (PropCalc a) (PropCalc a)
  | Imp (PropCalc a) (PropCalc a)
  deriving (Eq)

data FOL a =
  Eq (Arith a) (Arith a)
  | ForAll a (PropCalc (FOL a))
  | Exists a (PropCalc (FOL a))
  deriving (Eq)

data Command a =
  CSkip
  | CAssign a (Arith a)
  | CSequence (Command a) (Command a)
  | CIfElse (PropCalc (FOL a)) (Command a) (Command a)
  | CWhile (PropCalc (FOL a)) (Command a)
  | CAssert (PropCalc (FOL a)) (Command a) (PropCalc (FOL a))

instance Show a => Show (Proof a) where
  show (Proof a) = "|- " ++ show a

instance Show a => Show (Arith a) where
  show (Var a)     = show a
  show Z           = "0"
  show (S a)       = "S(" ++ show a ++ ")"
  show (Plus a b)  = "(" ++ show a ++ ")+(" ++ show b ++ ")"
  show (Mult a b)  = "(" ++ show a ++ ")*(" ++ show b ++ ")"

instance Show a => Show (PropCalc a) where
  show (PropVar a) = show a
  show (Not a)     = "~" ++ show a
  show (And a b)   = "<" ++ show a ++ "> /\\ <" ++ show b ++ ">"
  show (Or a b)    = "<" ++ show a ++ "> \\/ <" ++ show b ++ ">"
  show (Imp a b)   = "<" ++ show a ++ "> -> <" ++ show b ++ ">"

instance Show a => Show (FOL a) where
  show (Eq a b) = "(" ++ show a ++ ")=(" ++ show b ++ ")"
  show (ForAll x y) = "A" ++ show x ++ ":" ++ show y
  show (Exists x y) = "E" ++ show x ++ ":" ++ show y

instance Show a => Show (Command a) where
  show CSkip           = ";"
  show (CAssign x y)   = show x ++ " := " ++ show y ++ ";"
  show (CSequence x y) = show x ++ " " ++ show y
  show (CIfElse x y z) = "(If (" ++ show x ++ ") Then (" ++ show y ++ ") Else (" ++ show z ++ "));"
  show (CWhile x y)    = "(While (" ++ show x ++ ") Do {" ++ show y ++ "});"
  show (CAssert x y z) = "(Assert {" ++ show x ++ "} (" ++ show y ++ ") {" ++ show z ++ "});"
