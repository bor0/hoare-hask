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
hoareSkip q = HoareTriple q CSkip q

-- | Hoare assignment rule
hoareAssignment :: Char -> Aexp -> Bexp -> HoareTriple
hoareAssignment v e q =
  HoareTriple
  (substBexp q (aoptimize e) v)
  (CAssign v e)
  q

-- Q[E/V] is the result of replacing in Q all occurrences of V by E
substAexp :: Aexp -> Aexp -> Char -> Aexp
substAexp (AId x) e v      = if x == v then e else AId x
substAexp (APlus x y) e v  = APlus (substAexp x e v) (substAexp y e v)
substAexp (AMinus x y) e v = AMinus (substAexp x e v) (substAexp y e v)
substAexp (AMult x y) e v  = AMult (substAexp x e v) (substAexp y e v)
substAexp x e v            = x

-- Auxiliary replacement function for Bexps
substBexp :: Bexp -> Aexp -> Char -> Bexp
substBexp q@(BEq (AId x) (ANum 0)) (APlus (AId x2) (ANum y1)) v
  | x == x2 && x2 == v && y1 > 0 = BNot (BEq (AId x) (ANum 0))
  | otherwise                    = q
substBexp q@(BEq x y) e v  = BEq (aoptimize $ substAexp x e v) (aoptimize $ substAexp y e v)
substBexp q@(BLe x y) e v  = BLe (aoptimize $ substAexp x e v) (aoptimize $ substAexp y e v)
substBexp (BAnd b1 b2) e v = BAnd (substBexp b1 e v) (substBexp b2 e v)
substBexp (BNot b) e v     = BNot (substBexp b e v)
substBexp q _ _ = q

-- | Hoare consequence rule
hoareConsequence :: Bexp -> HoareTriple -> Bexp -> Either String HoareTriple
hoareConsequence p1 (HoareTriple p2 c q2) q1
  | boptimize p1 == p2 && q1 == q2 = Right $ HoareTriple p1 c q1
  | q1 == boptimize q2 && p1 == p2 = Right $ HoareTriple p1 c q1
hoareConsequence _ _ _ = Left "Cannot construct proof"

-- | Hoare sequence rule
hoareSequence :: HoareTriple -> HoareTriple -> Either String HoareTriple
hoareSequence (HoareTriple p c1 q1) (HoareTriple q2 c2 r)
  | q1 == q2  = Right $ HoareTriple p (CSequence c1 c2) r
hoareSequence _ _ = Left "Cannot construct proof"

-- | Hoare conditional rule
hoareConditional :: HoareTriple -> HoareTriple -> Either String HoareTriple
hoareConditional (HoareTriple (BAnd b1 p1) c1 q1) (HoareTriple (BAnd (BNot b2) p2) c2 q2)
  | b1 == b2 &&
    p1 == p2 &&
    q1 == q2  = Right $ HoareTriple p1 (CIfElse b1 c1 c2) q1
hoareConditional (HoareTriple (BAnd p1 b1) c1 q1) (HoareTriple (BAnd (BNot p2) b2) c2 q2)
  | b1 == b2 &&
    p1 == p2 &&
    q1 == q2  = Right $ HoareTriple p1 (CIfElse b1 c1 c2) q1
hoareConditional _ _ = Left "Cannot construct proof"

-- | Hoare while rule
hoareWhile :: HoareTriple -> Either String HoareTriple
hoareWhile (HoareTriple (BAnd b p1) c p2)
  | p1 == p2  = Right $ HoareTriple p1 (CWhile b c) (BAnd (BNot b) p1)
hoareWhile (HoareTriple (BAnd p1 b) c p2)
  | p1 == p2  = Right $ HoareTriple p1 (CWhile b c) (BAnd (BNot b) p1)
hoareWhile _ = Left "Cannot construct proof"
