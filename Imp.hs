module Imp where

import Common
import Gentzen
import TNT
import qualified Data.Map as M

data Command a =
  CSkip
  | CAssign a (Arith a)
  | CSequence (Command a) (Command a)
  | CIfElse (PropCalc (FOL a)) (Command a) (Command a)
  | CWhile (PropCalc (FOL a)) (Command a)
  | CAssert (PropCalc (FOL a)) (Command a) (PropCalc (FOL a))

instance Show a => Show (Command a) where
  show CSkip           = ";"
  show (CAssign x y)   = show x ++ " := " ++ show y ++ ";"
  show (CSequence x y) = show x ++ " " ++ show y
  show (CIfElse x y z) = "(If (" ++ show x ++ ") Then (" ++ show y ++ ") Else (" ++ show z ++ "));"
  show (CWhile x y)    = "(While (" ++ show x ++ ") Do {" ++ show y ++ "});"
  show (CAssert x y z) = "(Assert {" ++ show x ++ "} (" ++ show y ++ ") {" ++ show z ++ "});"

type Context a = M.Map a Integer

aeval :: (Ord a, Eq a) => Context a -> Arith a -> Integer
aeval ctx (Var v)        = ctx M.! v -- element may not exist
aeval ctx Z              = 0
aeval ctx (S x)          = aeval ctx x + 1
aeval ctx (Plus a1 a2)   = aeval ctx a1 + aeval ctx a2
aeval ctx (Mult a1 a2)   = aeval ctx a1 * aeval ctx a2

beval :: (Ord a, Eq a) => Context a -> PropCalc (FOL a) -> Bool
beval ctx (PropVar (Eq x y))     = aeval ctx x == aeval ctx y
beval ctx (PropVar (ForAll x y)) = beval ctx y
beval ctx (PropVar (Exists x y)) = beval ctx y
beval ctx (Not b1)               = not (beval ctx b1)
beval ctx (And b1 b2)            = beval ctx b1 && beval ctx b2
beval ctx (Or b1 b2)             = beval ctx b1 || beval ctx b2
beval ctx (Imp b1 b2)            = not (beval ctx b1) || beval ctx b2

eval :: (Ord a, Eq a) => Context a -> Command a -> Either String (Context a)
eval ctx CSkip             = Right ctx
eval ctx (CAssign c v)     = Right $ M.insert c (aeval ctx v) ctx
eval ctx (CSequence c1 c2) = let ctx' = eval ctx c1 in whenRight ctx' (\ctx'' -> eval ctx'' c2)
eval ctx (CIfElse b c1 c2) = eval ctx $ if beval ctx b then c1 else c2
eval ctx (CWhile b c)      =
  if beval ctx b
  then let ctx' = eval ctx c in whenRight ctx' (\ctx'' -> eval ctx'' (CWhile b c))
  else Right ctx
eval ctx (CAssert b1 c b2) =
  if beval ctx b1
  then whenRight (eval ctx c)
       (\ctx' -> if beval ctx' b2
                  then Right ctx'
                  else Left "Post-condition does not match!")
  else Left "Pre-condition does not match!"

assert :: (Ord a, Eq a) => Context a -> PropCalc (FOL a) -> Command a -> PropCalc (FOL a) -> Bool
assert ctx boolPre cmd boolPost = let res = eval ctx cmd in go res
  where
  go (Right ctx') = beval ctx boolPre && beval ctx' boolPost
  go _            = False
