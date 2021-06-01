module ExampleTNT where

import Common
import ExampleCommon
import Gentzen
import PrettyPrinter
import TNT
import Control.Monad (join)

-- | Session 1
-- |- <~<a> -> <b>> -> <<a> /\ <~b>>
lemma1 =
  -- |- All A:All B:(A+SB=S(A+B))
  axiom3 (Var A) (Var B) >>= \step1 ->
  -- |- All B:(D+SB=S(D+B))
  ruleSpec step1 (Var D) >>= \step2 ->
  -- |- D+SSC=S(D+SC)
  ruleSpec step2 (S (Var C)) >>= \step3 ->
  -- |- All B:(SD+SB=S(SD+B))
  ruleSpec step1 (S (Var D)) >>= \step4 ->
  -- |- SD+SC=S(SD+C)
  ruleSpec step4 (Var C) >>= \step5 ->
  -- |- S(SD+C)=SD+SC
  ruleSymmetry step5 >>= \step6 ->
  let f premise =
       -- |- D+SC=SD+C
       ruleSpec premise (Var D) >>= \step8 ->
       -- |- S(D+SC)=S(SD+C)
       ruleAddS step8 >>= \step9 ->
       -- |- D+SSC=S(SD+C)
       ruleTransitivity step3 step9 >>= \step10 ->
       -- |- D+SSC=SD+SC
       ruleTransitivity step10 step6 >>= \step11 ->
       -- |- All D:(D+SSC=SD+SC)
       ruleGeneralize step11 D (Just premise)
      -- All D:(D+SC=SD+C)
      premise = PropVar (ForAll D (PropVar (Eq (Plus (Var D) (S (Var C))) (Plus (S (Var D)) (Var C)))))
      -- |- All D:(D+SC=SD+C) -> All D:(D+SSC=SD+SC)
      in ruleFantasy f premise >>= \step7 ->
      -- lemma1 |- All C:<All D:(D+SC=SD+C) -> All D:(D+SSC=SD+SC)>
      ruleGeneralize step7 C Nothing

lemma2 =
  -- |- All A:All B:(A+SB=S(A+B))
  axiom3 (Var A) (Var B) >>= \step1 ->
  -- |- All B:(D+SB=S(D+B))
  ruleSpec step1 (Var D) >>= \step2 ->
  -- |- D+SSC=S(D+SC)
  ruleSpec step2 (S (Var C)) >>= \step3 ->
  -- |- D+S0=S(D+0)
  ruleSpec step2 Z >>= \step4 ->
  -- |- All A:(A+0=A)
  axiom2 (Var A) >>= \step5 ->
  -- |- D+0=D
  ruleSpec step5 (Var D) >>= \step6 ->
  -- |- S(D+0)=SD
  ruleAddS step6 >>= \step7 ->
  -- |- D+S0=SD
  ruleTransitivity step4 step7 >>= \step8 ->
  -- |- SD+0=SD
  ruleSpec step5 (S (Var D)) >>= \step9 ->
  -- |- SD=SD+0
  ruleSymmetry step9 >>= \step10 ->
  -- |- D+S0=SD+0
  ruleTransitivity step8 step10 >>= \step11 ->
  -- lemma2 |- All D:(D+S0=SD+0)
  ruleGeneralize step11 D Nothing

-- |- All C:All D:(D+SC=SD+C)
theorem = join $ ruleInduction <$> lemma2 <*> lemma1
