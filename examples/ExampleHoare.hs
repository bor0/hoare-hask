module ExampleHoare where

import Common
import ExampleCommon
import ExampleGentzen
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

pre = ruleFantasy f premise where
  premise = And (Not (PropVar $ Eq (Var A) (Var B))) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))
  -- |- ~A=B /\ Exists C:(A+C=B) -> Exists C:(SA+C)=B
  f premise = fromRight $ ruleExistence step6 C [] where
    -- |- ~~Exists C:(A+C=B)
    step1 = ruleDoubleTildeIntro (fromRight $ ruleSepR premise)
    -- |- ~~A+SC=B
    step2 = applyFOLRule [GoLeft] (\x -> fromRight $ ruleSpec (fromRight $ ruleInterchangeR x) (S (Var C))) step1 Nothing
    -- |- A+SC=B
    step3 = fromRight $ ruleDoubleTildeElim step2
    -- |- A+SC=SA+C
    step4 = fromRight $ ruleSpec (fromRight $ ruleSpec theorem (Var C)) (Var A)
    -- |- SA+C=A+SC
    step5 = fromRight $ ruleSymmetry step4
    -- |- SA+C=B
    step6 = fromRight $ ruleTransitivity step5 step3

-- |- Exists C:(A+C=B) -> Exists C:(A+C=B)
post = ruleFantasy id (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {Exists C:(SA+C=B)} A := SA; {Exists C:(A+C=B)}
step5 = hoareAssignment A (S (Var A)) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {~A=B /\ Exists C:(A+C=B)} A := SA; {Exists C:(A+C=B)}
step4 = fromRight $ hoareConsequence pre step5 post

-- {Exists C:(0+C=B)} A := 0; {Exists C:(A+C=B)}
step2 = hoareAssignment A Z (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {Exists C:(A+C=B)} (While (~A=B) Do {A := SA;}); {~~A=B /\ Exists C:(A+C=B)}
step3 = fromRight $ hoareWhile step4

-- {Exists C:(0+C=B)} A := 0; (While (~A=B) Do {A := SA;}); {~~A=B /\ Exists C:(A+C=B)}
proof = fromRight $ hoareSequence step2 step3
