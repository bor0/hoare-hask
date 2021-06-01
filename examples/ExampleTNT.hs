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
  step2 <- ruleSpec step1 (Var D)
  -- |- D+SSC=S(D+SC)
  step3 <- ruleSpec step2 (S (Var C))
  -- |- All B:(SD+SB=S(SD+B))
  step4 <- ruleSpec step1 (S (Var D))
  -- |- SD+SC=S(SD+C)
  step5 <- ruleSpec step4 (Var C)
  -- |- S(SD+C)=SD+SC
  step6 <- ruleSymmetry step5
  -- |- All D:(D+SC=SD+C) -> All D:(D+SSC=SD+SC)
  step7 <- ruleFantasy (PropVar (ForAll D (PropVar (Eq (Plus (Var D) (S (Var C))) (Plus (S (Var D)) (Var C)))))) $ \premise -> do
    -- |- D+SC=SD+C
    step8 <- ruleSpec premise (Var D)
    -- |- S(D+SC)=S(SD+C)
    step9 <- ruleAddS step8
    -- |- D+SSC=S(SD+C)
    step10 <- ruleTransitivity step3 step9
    -- |- D+SSC=SD+SC
    step11 <- ruleTransitivity step10 step6
    -- |- All D:(D+SSC=SD+SC)
    ruleGeneralize step11 D (Just premise)
  -- lemma1 |- All C:<All D:(D+SC=SD+C) -> All D:(D+SSC=SD+SC)>
  ruleGeneralize step7 C Nothing

lemma2 = do
  -- |- All A:All B:(A+SB=S(A+B))
  step1 <- axiom3 (Var A) (Var B)
  -- |- All B:(D+SB=S(D+B))
  step2 <- ruleSpec step1 (Var D)
  -- |- D+SSC=S(D+SC)
  step3 <- ruleSpec step2 (S (Var C))
  -- |- D+S0=S(D+0)
  step4 <- ruleSpec step2 Z
  -- |- All A:(A+0=A)
  step5 <- axiom2 (Var A)
  -- |- D+0=D
  step6 <- ruleSpec step5 (Var D)
  -- |- S(D+0)=SD
  step7 <- ruleAddS step6
  -- |- D+S0=SD
  step8 <- ruleTransitivity step4 step7
  -- |- SD+0=SD
  step9 <- ruleSpec step5 (S (Var D))
  -- |- SD=SD+0
  step10 <- ruleSymmetry step9
  -- |- D+S0=SD+0
  step11 <- ruleTransitivity step8 step10
  -- lemma2 |- All D:(D+S0=SD+0)
  ruleGeneralize step11 D Nothing

-- |- All C:All D:(D+SC=SD+C)
theorem = join $ ruleInduction <$> lemma2 <*> lemma1
