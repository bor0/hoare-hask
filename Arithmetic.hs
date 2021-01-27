module Arithmetic where

data Aexp =
  ANum Integer
  | AId Char
  | APlus Aexp Aexp
  | AMinus Aexp Aexp
  | AMult Aexp Aexp
  deriving (Eq)

instance Show Aexp where
  show (ANum x)     = show x
  show (AId x)      = [x]
  show (APlus x y)  = show x ++ " + " ++ show y
  show (AMinus x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (AMult x y)  = "(" ++ show x ++ " * " ++ show y ++ ")"

aoptimize :: Aexp -> Aexp
aoptimize q@(AMinus (APlus (AId a1) (AId a2)) (AId a3))  = if a2 == a3 then AId a1 else q
aoptimize q@(AMinus (AId a1) (AMinus (AId a2) (AId a3))) = if a1 == a2 then AId a3 else q
aoptimize (APlus (ANum a1) (ANum a2))  = ANum (a1 + a2)
aoptimize (AMinus (ANum a1) (ANum a2)) = ANum (a1 - a2)
aoptimize (AMult (ANum a1) (ANum a2))  = ANum (a1 * a2)
aoptimize x                            = x
