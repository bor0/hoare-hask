module Hoare where

import Common
import Gentzen
import Imp
import TNT

data HoareTriple a =
  HoareTriple (PropCalc (FOL a)) (Command a) (PropCalc (FOL a))
  deriving (Show)

instance Pretty a => Pretty (HoareTriple a) where
  pr (HoareTriple pre c post) = "{" ++ pr pre ++ "} " ++ pr c ++ " {" ++ pr post ++ "}"

-- | Hoare skip rule
hoareSkip :: PropCalc (FOL a) -> HoareTriple a
hoareSkip q = HoareTriple q CSkip q

-- | Hoare assignment rule
hoareAssignment :: Eq a => a -> Arith a -> PropCalc (FOL a) -> HoareTriple a
hoareAssignment v e q =
  HoareTriple
  (fromProof (substPropCalc (Proof q) (Var v) e))
  (CAssign v e)
  q

-- | Hoare consequence rule
hoareConsequence :: Eq a => Proof (PropCalc (FOL a)) -> HoareTriple a -> Proof (PropCalc (FOL a)) -> Either String (HoareTriple a)
hoareConsequence (Proof (Imp p1 p2)) (HoareTriple p2' c q2) (Proof (Imp q2' q1))
  | p2 == p2' && q2 == q2' = Right $ HoareTriple p1 c q1
hoareConsequence _ _ _ = Left "hoareConsequence: Cannot construct proof"

-- | Hoare sequence rule
hoareSequence :: Eq a => HoareTriple a -> HoareTriple a -> Either String (HoareTriple a)
hoareSequence (HoareTriple p c1 q1) (HoareTriple q2 c2 r)
  | q1 == q2  = Right $ HoareTriple p (CSequence c1 c2) r
hoareSequence _ _ = Left "hoareSequence: Cannot construct proof"

-- | Hoare conditional rule
hoareConditional :: Eq a => HoareTriple a -> HoareTriple a -> Either String (HoareTriple a)
hoareConditional (HoareTriple (And b1 p1) c1 q1) (HoareTriple (And (Not b2) p2) c2 q2)
  | b1 == b2 &&
    p1 == p2 &&
    q1 == q2  = Right $ HoareTriple p1 (CIfElse b1 c1 c2) q1
hoareConditional (HoareTriple (And p1 b1) c1 q1) (HoareTriple (And (Not p2) b2) c2 q2)
  | b1 == b2 &&
    p1 == p2 &&
    q1 == q2  = Right $ HoareTriple p1 (CIfElse b1 c1 c2) q1
hoareConditional _ _ = Left "hoareConditional: Cannot construct proof"

-- | Hoare while rule
hoareWhile :: Eq a => HoareTriple a -> Either String (HoareTriple a)
hoareWhile (HoareTriple (And b p1) c p2)
  | p1 == p2  = Right $ HoareTriple p1 (CWhile b c) (And (Not b) p1)
hoareWhile (HoareTriple (And p1 b) c p2)
  | p1 == p2  = Right $ HoareTriple p1 (CWhile b c) (And (Not b) p1)
hoareWhile _ = Left "hoareWhile: Cannot construct proof"
