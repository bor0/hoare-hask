module ExampleTNT where

import Common
import ExampleCommon
import Gentzen
import PrettyPrinter
import TNT

lemma1 =
  -- |- All A:All B:(A+SB=S(A+B))
  let step1 = axiom3 A B
      -- |- All B:(D+SB=S(D+B))
      step2 = fromRight $ ruleSpec step1 (Var D)
      -- |- D+SSC=S(D+SC)
      step3 = fromRight $ ruleSpec step2 (S (Var C))
      -- |- All B:(SD+SB=S(SD+B))
      step4 = fromRight $ ruleSpec step1 (S (Var D))
      -- |- SD+SC=S(SD+C)
      step5 = fromRight $ ruleSpec step4 (Var C)
      -- |- S(SD+C)=SD+SC
      step6 = fromRight $ ruleSymmetry step5
      -- All D:(D+SC=SD+C)
      premise = PropVar (ForAll D (PropVar (Eq (Plus (Var D) (S (Var C))) (Plus (S (Var D)) (Var C)))))
      f premise =
       -- |- D+SC=SD+C
       let step8 = fromRight $ ruleSpec premise (Var D)
           -- |- S(D+SC)=S(SD+C)
           step9 = fromRight $ ruleAddS step8
           -- |- D+SSC=S(SD+C)
           step10 = fromRight $ ruleTransitivity step3 step9
           -- |- D+SSC=SD+SC
           step11 = fromRight $ ruleTransitivity step10 step6
           -- |- All D:(D+SSC=SD+SC)
           in fromRight $ ruleGeneralize step11 D (Just premise)
      -- |- All D:(D+SC=SD+C) -> All D:(D+SSC=SD+SC)
      step7 = ruleFantasy f premise
      -- lemma1 |- All C:<All D:(D+SC=SD+C) -> All D:(D+SSC=SD+SC)>
      in fromRight $ ruleGeneralize step7 C Nothing

lemma2 =
  -- |- All A:All B:(A+SB=S(A+B))
  let step1 = axiom3 A B
      -- |- All B:(D+SB=S(D+B))
      step2 = fromRight $ ruleSpec step1 (Var D)
      -- |- D+SSC=S(D+SC)
      step3 = fromRight $ ruleSpec step2 (S (Var C))
      -- |- D+S0=S(D+0)
      step4 = fromRight $ ruleSpec step2 Z
      -- |- All A:(A+0=A)
      step5 = axiom2 A
      -- |- D+0=D
      step6 = fromRight $ ruleSpec step5 (Var D)
      -- |- S(D+0)=SD
      step7 = fromRight $ ruleAddS step6
      -- |- D+S0=SD
      step8 = fromRight $ ruleTransitivity step4 step7
      -- |- SD+0=SD
      step9 = fromRight $ ruleSpec step5 (S (Var D))
      -- |- SD=SD+0
      step10 = fromRight $ ruleSymmetry step9
      -- |- D+S0=SD+0
      step11 = fromRight $ ruleTransitivity step8 step10
      -- lemma2 |- All D:(D+S0=SD+0)
      in fromRight $ ruleGeneralize step11 D Nothing

-- |- All C:All D:(D+SC=SD+C)
theorem = fromRight $ ruleInduction lemma2 lemma1
