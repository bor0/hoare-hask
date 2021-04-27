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

-- |- <<~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>> -> <Exists C:((S(A))+(C))=(B)>
pre = ruleFantasy f premise where
  premise = And (Not (PropVar $ Eq (Var A) (Var B))) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))
  -- |- <<~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>> -> <Exists C:((S(A))+(C))=(B)>
  f premise = fromRight $ ruleExistence step6 C [] where
    -- |- ~~Exists C:((A)+(C))=(B)
    step1 = ruleDoubleTildeIntro (fromRight $ ruleSepR premise)
    -- |- ~~((A)+(S(C)))=(B)
    step2 = applyFOLRule [GoLeft] (\x -> fromRight $ ruleSpec (fromRight $ ruleInterchangeR x) C (S (Var C))) step1
    -- |- ((A)+(S(C)))=(B)
    step3 = fromRight $ ruleDoubleTildeElim step2
    -- |- ((A)+(S(C)))=((S(A))+(C))
    step4 = fromRight $ ruleSpec (fromRight $ ruleSpec theorem C (Var C)) D (Var A)
    -- |- ((S(A))+(C))=((A)+(S(C)))
    step5 = fromRight $ ruleSymmetry step4
    -- |- ((S(A))+(C))=(B)
    step6 = fromRight $ ruleTransitivity step5 step3

-- |- <Exists C:((A)+(C))=(B)> -> <Exists C:((A)+(C))=(B)>
post = ruleFantasy id (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {Exists C:((S(A))+(C))=(B)} A := S(A); {Exists C:((A)+(C))=(B)}
step5 = hoareAssignment A (S (Var A)) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {<~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>} A := S(A); {Exists C:((A)+(C))=(B)}
step4 = fromRight $ hoareConsequence pre step5 post

-- {Exists C:((0)+(C))=(B)} A := 0; {Exists C:((A)+(C))=(B)}
step2 = hoareAssignment A Z (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {Exists C:((A)+(C))=(B)} (While (~(A)=(B)) Do {A := S(A);}); {<~~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>}
step3 = fromRight $ hoareWhile step4

-- {Exists C:((0)+(C))=(B)} A := 0; (While (~(A)=(B)) Do {A := S(A);}); {<~~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>}
step1 = fromRight $ hoareSequence step2 step3
