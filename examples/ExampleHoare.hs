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

pre = ruleFantasy f premise where
  premise = And (Not (PropVar $ Eq (Var A) (Var B))) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))
  -- |- ~A=B /\ Exists C:(A+C=B) -> Exists C:(SA+C)=B
  f premise = go >>= \go -> ruleExistence go C [] where
    -- |- ~~Exists C:(A+C=B)
    go = ruleSepR premise >>= \foo -> ruleDoubleTildeIntro foo >>= \step1 ->
         -- |- ~~A+SC=B
         applyFOLRule [GoLeft] (\x -> ruleInterchangeR x >>= \rir -> ruleSpec rir (S (Var C))) step1 Nothing >>= \step2 ->
         -- |- A+SC=B
         ruleDoubleTildeElim step2 >>= \step3 ->
         -- |- A+SC=SA+C
         (theorem >>= \theorem -> ruleSpec theorem (Var C)) >>= \thm -> ruleSpec thm (Var A) >>= \step4 ->
         -- |- SA+C=A+SC
         ruleSymmetry step4 >>= \step5 ->
         -- |- SA+C=B
         ruleTransitivity step5 step3

-- |- Exists C:(A+C=B) -> Exists C:(A+C=B)
post = ruleFantasy Right (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

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
