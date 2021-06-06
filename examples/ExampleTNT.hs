module ExampleTNT where

import Common
import ExampleCommon
import Gentzen
import PrettyPrinter
import TNT
import Control.Monad (join)

lemma1 = do
  -- |- All A:All B:(A+SB=S(A+B))
  step1 <- axiom3 (Var A) (Var B)
  -- |- All B:(D+SB=S(D+B))
  step2 <- ruleSpec (Var D) step1
  -- |- D+SSC=S(D+SC)
  step3 <- ruleSpec (S (Var C)) step2
  -- |- All B:(SD+SB=S(SD+B))
  step4 <- ruleSpec (S (Var D)) step1
  -- |- SD+SC=S(SD+C)
  step5 <- ruleSpec (Var C) step4
  -- |- S(SD+C)=SD+SC
  step6 <- ruleSymmetry step5
  -- |- All D:(D+SC=SD+C) -> All D:(D+SSC=SD+SC)
  step7 <- ruleFantasy (PropVar (ForAll D (PropVar (Eq (Plus (Var D) (S (Var C))) (Plus (S (Var D)) (Var C)))))) $ \premise -> do
    -- |- D+SC=SD+C
    step8 <- ruleSpec (Var D) premise
    -- |- S(D+SC)=S(SD+C)
    step9 <- ruleAddS step8
    -- |- D+SSC=S(SD+C)
    step10 <- ruleTransitivity step3 step9
    -- |- D+SSC=SD+SC
    step11 <- ruleTransitivity step10 step6
    -- |- All D:(D+SSC=SD+SC)
    ruleGeneralize D [premise] step11
  -- lemma1 |- All C:<All D:(D+SC=SD+C) -> All D:(D+SSC=SD+SC)>
  ruleGeneralize C [] step7

lemma2 = do
  -- |- All A:All B:(A+SB=S(A+B))
  step1 <- axiom3 (Var A) (Var B)
  -- |- All B:(D+SB=S(D+B))
  step2 <- ruleSpec (Var D) step1
  -- |- D+SSC=S(D+SC)
  step3 <- ruleSpec (S (Var C)) step2
  -- |- D+S0=S(D+0)
  step4 <- ruleSpec Z step2
  -- |- All A:(A+0=A)
  step5 <- axiom2 (Var A)
  -- |- D+0=D
  step6 <- ruleSpec (Var D) step5
  -- |- S(D+0)=SD
  step7 <- ruleAddS step6
  -- |- D+S0=SD
  step8 <- ruleTransitivity step4 step7
  -- |- SD+0=SD
  step9 <- ruleSpec (S (Var D)) step5
  -- |- SD=SD+0
  step10 <- ruleSymmetry step9
  -- |- D+S0=SD+0
  step11 <- ruleTransitivity step8 step10
  -- lemma2 |- All D:(D+S0=SD+0)
  ruleGeneralize D [] step11

-- |- All C:All D:(D+SC=SD+C)
theorem = join $ ruleInduction <$> lemma2 <*> lemma1
