module ExampleHoare where

import Common
import Control.Monad (join)
import ExampleCommon
import ExampleTNT
import Gentzen
import Hoare
import Imp
import PrettyPrinter
import TNT
import qualified Data.Map as M

-- Program definition
countToB =
  let l1 = CAssign A Z
      l2 = CWhile (Not (PropVar $ Eq (Var A) (Var B))) l3
      l3 = CAssign A (S (Var A))
  in CSequence l1 l2

-- Example evaluation
egEval = eval (M.fromList [(B, 3)]) countToB

pre = ruleFantasy (And (Not (PropVar $ Eq (Var A) (Var B))) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))) $ \premise -> do
    step1 <- ruleSepR premise
    -- |- ~~Exists C:(A+C=B)
    step1 <- ruleDoubleTildeIntro step1
    -- |- ~~A+SC=B
    step2 <- applyFOLRule [GoLeft] (\x -> ruleInterchangeR x >>= \prf -> ruleSpec prf (S (Var C))) step1 []
    -- |- A+SC=B
    step3 <- ruleDoubleTildeElim step2
    step4 <- theorem >>= \theorem -> ruleSpec theorem (Var C)
    -- |- A+SC=SA+C
    step4 <- ruleSpec step4 (Var A)
    -- |- SA+C=A+SC
    step5 <- ruleSymmetry step4
    -- |- SA+C=B
    step6 <- ruleTransitivity step5 step3
    -- |- ~A=B /\ Exists C:(A+C=B) -> Exists C:(SA+C)=B
    ruleExistence step6 C []

-- |- Exists C:(A+C=B) -> Exists C:(A+C=B)
post = ruleFantasy (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B)))) Right

-- {Exists C:(SA+C=B)} A := SA; {Exists C:(A+C=B)}
step5 = hoareAssignment A (S (Var A)) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {~A=B /\ Exists C:(A+C=B)} A := SA; {Exists C:(A+C=B)}
step4 = join $ hoareConsequence <$> pre <*> step5 <*> post

-- {Exists C:(0+C=B)} A := 0; {Exists C:(A+C=B)}
step2 = hoareAssignment A Z (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {Exists C:(A+C=B)} (While (~A=B) Do {A := SA;}); {~~A=B /\ Exists C:(A+C=B)}
step3 = join $ hoareWhile <$> step4

-- {Exists C:(0+C=B)} A := 0; (While (~A=B) Do {A := SA;}); {~~A=B /\ Exists C:(A+C=B)}
proof = join $ hoareSequence <$> step2 <*> step3
