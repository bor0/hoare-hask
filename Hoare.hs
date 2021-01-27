module Hoare where

import Arithmetic
import Boolean
import Command

data HoareTriple =
  HoareTriple Bexp Command Bexp

instance Show HoareTriple where
  show (HoareTriple pre c post) = "{" ++ show pre ++ "} " ++ show c ++ " {" ++ show post ++ "}"

-- | Hoare skip rule
hoareSkip :: Bexp -> HoareTriple
hoareSkip q = HoareTriple (boptimize q) CSkip (boptimize q)

-- | Hoare assignment rule
hoareAssignment :: Char -> Aexp -> Bexp -> HoareTriple
hoareAssignment v e q =
  HoareTriple
  (boptimize (substAssignment (boptimize q) (aoptimize e) v))
  (CAssign v e)
  (boptimize q)

substAexp :: Aexp -> Char -> Aexp -> Aexp
substAexp (AId x) v e      = if x == v then e else (AId x)
substAexp (APlus x y) v e  = APlus (substAexp x v e) (substAexp y v e)
substAexp (AMinus x y) v e = AMinus (substAexp x v e) (substAexp y v e)
substAexp (AMult x y) v e  = AMult (substAexp x v e) (substAexp y v e)
substAexp x e v            = x--if x == v then (AId e) else x

-- Q[E/V] is the result of replacing in Q all occurrences of V by E
substAssignment :: Bexp -> Aexp -> Char -> Bexp
substAssignment q@(BEq (AId x) (ANum 0)) (APlus (AId x2) (ANum y1)) v
  | x == x2 && x2 == v && y1 > 0 = BNot (BEq (AId x) (ANum 0))
  | otherwise                    = q
substAssignment q@(BEq x y) e v = BEq (substAexp x v e) (substAexp y v e)
substAssignment q@(BLe x y) e v = BLe (substAexp x v e) (substAexp y v e)
substAssignment (BAnd b1 b2) e v      = BAnd (substAssignment b1 e v) (substAssignment b2 e v)
substAssignment (BNot b) e v          = BNot (substAssignment b e v)
substAssignment q _ _ = q

-- | Hoare sequence rule
hoareSequence :: HoareTriple -> HoareTriple -> Either String HoareTriple
hoareSequence (HoareTriple p c1 q1) (HoareTriple q2 c2 r)
  | boptimize q1 == boptimize q2 = Right $ HoareTriple (boptimize p) (CSequence c1 c2) (boptimize r)
  | otherwise                    = Left "Cannot construct proof"

-- | Hoare conditional rule
hoareConditional :: HoareTriple -> HoareTriple -> Either String HoareTriple
hoareConditional (HoareTriple (BAnd b1 p1) c1 q1) (HoareTriple (BAnd (BNot b2) p2) c2 q2)
  | boptimize b1 == boptimize b2 &&
    boptimize p1 == boptimize p2 &&
    boptimize q1 == boptimize q2 = Right $ HoareTriple (boptimize p1) (CIfElse b1 c1 c2) (boptimize q1)
hoareConditional (HoareTriple (BAnd p1 b1) c1 q1) (HoareTriple (BAnd (BNot p2) b2) c2 q2)
  | boptimize b1 == boptimize b2 &&
    boptimize p1 == boptimize p2 &&
    boptimize q1 == boptimize q2 = Right $ HoareTriple (boptimize p1) (CIfElse b1 c1 c2) (boptimize q1)
  | otherwise                    = Left "Cannot construct proof"
hoareConditional _ _ = Left "Cannot construct proof"
