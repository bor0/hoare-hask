module ExampleTNT2 where

import Common
import Control.Monad (join)
import ExampleCommon
import Gentzen
import PrettyPrinter
import TNT

main = do
  putStrLn "Addition"
  mapM_ (\(n,p) -> putStrLn $ show n ++ ": " ++ pr p) $ zip [1..] [prop1,prop2,prop3,prop4,prop5]
  putStrLn "Multiplication"
  mapM_ (\(n,p) -> putStrLn $ show n ++ ": " ++ pr p) $ zip [6..] [prop6,prop7,prop8]
  putStrLn "Example strictness of `applyFOLRule`"
  putStrLn $ pr $ let formula = Proof $ And (PropVar $ Eq (Var A) (Var B)) (PropVar $ Exists B (PropVar (Eq (Var B) (Var C)))) in applyFOLRule [GoLeft] (\prfAeqB -> applyFOLRule [GoRight,GoLeft] (ruleTransitivity prfAeqB) [] formula) [] formula
  putStrLn $ pr $ let formula = Proof $ And (PropVar $ Eq (Var A) (Var B)) (PropVar $ Exists B (PropVar (Eq (Var B) (Var C)))) in applyFOLRule [GoLeft] (\prfAeqB -> applyFOLRule [GoRight,GoLeft] (ruleTransitivity prfAeqB) [prfAeqB] formula) [] formula

{- Prop1 -}
-- |- 0=0+0
prop1base = do
  step1 <- axiom2 (Var A)
  step2 <- ruleSpec Z step1
  ruleSymmetry step2

-- |- All A:<A=0+A -> SA=0+SA>
prop1hyp = do
  imp <- ruleFantasy (PropVar (Eq (Var A) (Plus Z (Var A)))) $ \premise -> do
    -- |- A=0+A -> SA=S(0+A)
    eq1 <- ruleAddS premise
    step1 <- axiom3 (Var A) (Var B)
    step2 <- ruleSpec Z step1
    step3 <- ruleSpec (Var A) step2
    -- |- S(0+A)=0+SA
    eq2 <- ruleSymmetry step3
    ruleTransitivity eq1 eq2
  ruleGeneralize A [] imp

-- |- All A:(A=0+A)
prop1 = join $ ruleInduction <$> prop1base <*> prop1hyp

{- Prop2 -}
-- |- SA+0=S(A+0)
prop2base = do
  -- |- SA+0=SA
  step1 <- axiom2 (Var A)
  eq1 <- ruleSpec (S (Var A)) step1
  -- |- A+0=A
  eq2 <- ruleSpec (Var A) step1
  -- |- S(A+0)=SA
  eq2' <- ruleAddS eq2
  -- |- SA=S(A+0)
  eq2'' <- ruleSymmetry eq2'
  ruleTransitivity eq1 eq2''

-- |- All A:<SA+B=S(A+B) -> SA+SB=S(A+SB)>
prop2hyp = do
  imp <- ruleFantasy (PropVar (Eq (Plus (S (Var A)) (Var B)) (S (Plus (Var A) (Var B))))) $ \premise -> do
    -- |- SA+SB=S(SA+B)
    step1 <- axiom3 (Var A) (Var B)
    eq1 <- ruleSpec (S (Var A)) step1
    eq1 <- ruleSpec (Var B) eq1
    -- |- S(SA+B)=SS(A+B)
    eq2 <- ruleAddS premise
    -- |- SA+SB=SS(A+B)
    eq3 <- ruleTransitivity eq1 eq2
    -- |- A+SB=S(A+B)
    eq4 <- ruleSpec (Var A) step1
    eq4 <- ruleSpec (Var B) eq4
    -- |- S(A+SB)=SS(A+B)
    eq4' <- ruleAddS eq4
    -- |- SS(A+B)=S(A+SB)
    eq4'' <- ruleSymmetry eq4'
    ruleTransitivity eq3 eq4''
  ruleGeneralize B [] imp

-- |- All A:All B:(SA+B=S(A+B))
prop2 = join (ruleInduction <$> prop2base <*> prop2hyp) >>= ruleGeneralize A []

{- Prop3 -}
-- |- B=C -> 0+B=0+C
prop3base = ruleFantasy (PropVar (Eq (Var B) (Var C))) $ \premise -> do
  prop1 <- prop1
  step1 <- ruleSpec (Var B) prop1
  -- |- 0+B=B
  eq1 <- ruleSymmetry step1
  -- |- C=0+C
  eq2 <- ruleSpec (Var C) prop1
  -- |- 0+B=C
  eq3 <- ruleTransitivity eq1 premise
  ruleTransitivity eq3 eq2

-- |- All A:<<B=C -> A+B=A+C> -> B=C -> SA+B=SA+C>
prop3hyp = do
  imp <- ruleFantasy (Imp (PropVar (Eq (Var B) (Var C))) (PropVar (Eq (Plus (Var A) (Var B)) (Plus (Var A) (Var C))))) $ \premise -> do
   ruleFantasy (PropVar (Eq (Var B) (Var C))) $ \premise2 -> do
     prop2 <- prop2
     prop2 <- ruleSpec (Var A) prop2
     -- |- A+B=A+C
     eq1 <- ruleDetachment premise2 premise
     -- |- S(A+B)=S(A+C)
     eq2 <- ruleAddS eq1
     -- |- SA+B=S(A+B)
     eq3 <- ruleSpec (Var B) prop2
     eq3' <- ruleSpec (Var C) prop2
     -- |- S(A+C)=SA+C
     eq4 <- ruleSymmetry eq3'
     -- |- SA+B=S(A+C)
     eq5 <- ruleTransitivity eq3 eq2
     ruleTransitivity eq5 eq4
  ruleGeneralize A [] imp

-- |- All A:All B:All C:<B=C -> A+B=A+C>
prop3 = do
  eq1 <- join (ruleInduction <$> prop3base <*> prop3hyp)
  -- |- B=C -> A+B=A+C
  eq1 <- ruleSpec (Var A) eq1
  -- |- All C:<B=C -> A+B=A+C>
  eq2 <- ruleGeneralize C [] eq1
  -- |- All B:All C:<B=C -> A+B=A+C>
  eq3 <- ruleGeneralize B [] eq2
  ruleGeneralize A [] eq3

{- Prop4 -}
-- |- A+0=0+A
prop4base = do
  ax2 <- axiom2 (Var A)
  prop1 <- prop1
  eq1 <- ruleSpec (Var A) ax2
  eq2 <- ruleSpec (Var A) prop1
  ruleTransitivity eq1 eq2

-- |- All B:<A+B=B+A -> A+SB=SB+A>
prop4hyp = do
  imp <- ruleFantasy (PropVar (Eq (Plus (Var A) (Var B)) (Plus (Var B) (Var A)))) $ \premise -> do
    ax3 <- axiom3 (Var A) (Var B)
    step1 <- ruleSpec (Var A) ax3
    prop2 <- prop2
    -- |- A+SB=S(A+B)
    eq1 <- ruleSpec (Var B) step1
    -- |- S(A+B)=S(B+A)
    eq2 <- ruleAddS premise
    -- |- A+SB=S(B+A)
    eq3 <- ruleTransitivity eq1 eq2
    step2 <- ruleSpec (Var C) prop2
    step2 <- ruleSpec (Var A) step2
    step2 <- ruleGeneralize C [premise] step2
    -- |- SB+A=S(B+A)
    eq4 <- ruleSpec (Var B) step2
    -- |- S(B+A)=SB+A
    eq4' <- ruleSymmetry eq4
    ruleTransitivity eq3 eq4'
  ruleGeneralize B [] imp

-- |- All A:All B:(A+B=B+A)
prop4 = do
  -- |- All B:(A+B=B+A)
  eq1 <- join (ruleInduction <$> prop4base <*> prop4hyp)
  ruleGeneralize A [] eq1

{- Prop5 -}
-- |- A+B+0=(A+B)+0
prop5base = do
  ax2 <- axiom2 (Var A)
  prop3 <- prop3
  -- |- B+0=B
  eq1 <- ruleSpec (Var B) ax2
  -- |- B+0=B -> A+B+0=A+B
  eq2 <- ruleSpec (Var A) prop3
  eq2 <- ruleSpec (Plus (Var B) Z) eq2
  eq2 <- ruleSpec (Var B) eq2
  -- |- A+B+0=A+B
  eq3 <- ruleDetachment eq1 eq2
  -- |- A+B=(A+B)+0
  eq4 <- ruleSpec (Plus (Var A) (Var B)) ax2
  eq4 <- ruleSymmetry eq4
  -- |- A+B+0=(A+B)+0
  eq5 <- ruleTransitivity eq3 eq4
  ruleTransitivity eq3 eq4

-- |- All C:<A+B+C=(A+B)+C -> A+B+SC=(A+B)+SC>
prop5hyp = do
  imp <- ruleFantasy (PropVar (Eq (Plus (Var A) (Plus (Var B) (Var C))) (Plus (Plus (Var A) (Var B)) (Var C)))) $ \premise -> do
    ax3 <- axiom3 (Var A) (Var B)
    prop3 <- prop3
    -- |- B+SC=S(B+C)
    eq1 <- applyFOLRule [GoRight] (ruleSpec (Var C)) [] ax3
    eq1 <- ruleSpec (Var B) eq1
    -- |- B=S(D+C) -> A+B=A+S(D+C)
    eq2 <- ruleSpec (Var A) prop3
    eq2 <- ruleSpec (Var E) eq2
    eq2 <- ruleSpec (S (Plus (Var D) (Var C))) eq2
    -- |- B+SC=S(D+C) -> A+B+SC=A+S(D+C)
    eq2' <- ruleGeneralize E [premise] eq2
    eq2' <- ruleSpec (Plus (Var B) (S (Var C))) eq2'
    -- |- B+SC=S(B+C) -> A+B+SC=A+S(B+C)
    eq2'' <- ruleGeneralize D [premise] eq2'
    eq2'' <- ruleSpec (Var B) eq2''
    -- |- A+B+SC=A+S(B+C)
    eq3 <- ruleDetachment eq1 eq2''
    -- |- A+S(B+C)=S(A+B+C)
    eq4 <- ruleSpec (Var A) ax3
    eq4 <- ruleSpec (Plus (Var B) (Var C)) eq4
    -- |- A+B+SC=S(A+B+C)
    eq5 <- ruleTransitivity eq3 eq4
    -- |- S(A+B+C)=S((A+B)+C)
    eq6 <- ruleAddS premise
    -- |- A+B+SC=S((A+B)+C)
    eq7 <- ruleTransitivity eq5 eq6
    -- |- S((A+B)+C)=(A+B)+SC
    eq8 <- applyFOLRule [GoRight] (ruleSpec (Var C)) [] ax3
    eq8 <- ruleSpec (Plus (Var A) (Var B)) eq8
    eq8 <- ruleSymmetry eq8
    ruleTransitivity eq7 eq8
  ruleGeneralize C [] imp

-- |- All A:All B:All C:(A+B+C=(A+B)+C)
prop5 = do
  -- |- All C:(A+B+C=(A+B)+C
  eq1 <- join (ruleInduction <$> prop5base <*> prop5hyp)
  -- |- All B:All C:(A+B+C=(A+B)+C)
  eq2 <- ruleGeneralize B [] eq1
  ruleGeneralize A [] eq2

{- Prop6 -}
-- |- 0*0=0
prop6base = do
  ax4 <- axiom4 (Var A)
  ruleSpec Z ax4

-- |- All A:<0*A=0 -> 0*SA=0>
prop6hyp = do
  imp <- ruleFantasy (PropVar (Eq (Mult Z (Var A)) Z)) $ \premise -> do
    ax5 <- axiom5 (Var A) (Var B)
    ax2 <- axiom2 (Var A)
    eq1 <- ruleSpec Z ax5
    -- |- 0*SA=0*A+0
    eq2 <- ruleSpec (Var A) eq1
    -- |- 0*A+0=0*A
    eq3 <- ruleSpec (Mult Z (Var A)) ax2
    -- |- 0*SA=0*A
    eq4 <- ruleTransitivity eq2 eq3
    ruleTransitivity eq4 premise
  ruleGeneralize A [] imp

-- |- All A:(0*A=0)
prop6 = join (ruleInduction <$> prop6base <*> prop6hyp)

{- Prop7 -}
-- |- SA*0=A*0+0
prop7base = do
  ax4 <- axiom4 (Var A)
  ax2 <- axiom2 (Var A)
  prop3 <- prop3
  prop4 <- prop4
  -- |- SA*0=0
  eq1 <- ruleSpec (S (Var A)) ax4
  -- |- 0=0+0
  eq2 <- ruleSpec Z ax2
  eq2 <- ruleSymmetry eq2
  -- |- SA*0=0+0
  eq2' <- ruleTransitivity eq1 eq2
  -- |- A*0=0
  eq3 <- ruleSpec (Var A) ax4
  eq4 <- ruleSpec Z prop3
  eq4 <- ruleSpec (Mult (Var A) Z) eq4
  eq4 <- ruleSpec Z eq4
  -- |- 0+0=0+A*0
  eq4' <- ruleDetachment eq3 eq4
  eq4' <- ruleSymmetry eq4'
  -- |- SA*0=0+0
  eq5 <- ruleTransitivity eq1 eq2
  -- |- SA*0=0+A*0
  eq6 <- ruleTransitivity eq5 eq4'
  -- |- 0+A*0=A*0+0
  eq7 <- ruleSpec Z prop4
  eq7 <- ruleSpec (Mult (Var A) Z) eq7
  ruleTransitivity eq6 eq7

-- |- All B:<SA*B=A*B+B -> SA*SB=A*SB+SB>
prop7hyp = do
  imp <- ruleFantasy (PropVar (Eq (Mult (S (Var A)) (Var B)) (Plus (Mult (Var A) (Var B)) (Var B)))) $ \premise -> do
    ax3 <- axiom3 (Var A) (Var B)
    ax5 <- axiom5 (Var A) (Var B)
    prop3 <- prop3
    prop4 <- prop4
    prop5 <- prop5
    -- |- SA*SB=SA*B+SA
    eq1 <- ruleSpec (S (Var A)) ax5
    eq1 <- ruleSpec (Var B) eq1
    -- |- SA*B+SA=SA+SA*B
    eq2 <- ruleSpec (Var D) prop4
    eq2 <- ruleSpec (S (Var A)) eq2
    eq2 <- ruleGeneralize D [premise] eq2
    eq2 <- ruleSpec (Mult (S (Var A)) (Var B)) eq2
    eq2' <- ruleTransitivity eq1 eq2
    eq3 <- ruleSpec (S (Var A)) prop3
    eq3 <- ruleSpec (Mult (S (Var A)) (Var B)) eq3
    eq3 <- ruleSpec (Plus (Mult (Var A) (Var B)) (Var B)) eq3
    eq3' <- ruleDetachment premise eq3
    -- |- SA*SB=SA+A*B+B
    eq4 <- ruleTransitivity eq2' eq3'
    -- |- SA+A*B+B=(A*B+B)+SA
    eq5 <- ruleSpec (Var D) prop4
    eq5 <- ruleSpec (Plus (Mult (Var A) (Var B)) (Var B)) eq5
    eq5 <- ruleGeneralize D [premise] eq5
    eq5 <- ruleSpec (S (Var A)) eq5
    -- |- SA*SB=(A*B+B)+SA
    eq6 <- ruleTransitivity eq4 eq5
    -- |- A*B+B+SA=(A*B+B)+SA
    eq7 <- applyFOLRule [GoRight] (ruleSpec (Var B)) [] prop5
    eq7 <- ruleSpec (Mult (Var A) (Var B)) eq7
    eq7 <- ruleSpec (S (Var A)) eq7
    eq7 <- ruleSymmetry eq7
    -- |- SA*SB=A*B+B+SA
    eq8 <- ruleTransitivity eq6 eq7
    -- |- B+SA=S(B+A)
    eq9 <- ruleSpec (Var D) ax3
    eq9 <- ruleSpec (Var A) eq9
    eq9 <- ruleGeneralize D [premise] eq9
    eq9 <- ruleSpec (Var B) eq9
    -- |- B+SA=S(B+A) -> SA+B+SA=SA+S(B+A)
    eq9' <- ruleSpec (Var D) prop3
    eq9' <- ruleSpec (Plus (Var B) (S (Var A))) eq9'
    eq9' <- ruleSpec (S (Plus (Var B) (Var A))) eq9'
    eq9' <- ruleGeneralize D [premise] eq9'
    eq9' <- ruleSpec (Mult (Var A) (Var B)) eq9'
    -- |- A*B+B+SA=A*B+S(B+A)
    eq9'' <- ruleDetachment eq9 eq9'
    -- |- SA*SB=A*B+S(B+A)
    eq10 <- ruleTransitivity eq8 eq9''
    -- |- S(B+A)=S(A+B)
    eq11 <- ruleSpec (Var D) prop4
    eq11 <- ruleSpec (Var A) eq11
    eq11 <- ruleGeneralize D [premise] eq11
    eq11 <- ruleSpec (Var B) eq11
    eq11 <- ruleAddS eq11
    -- |- S(B+A)=S(A+B) -> A*B+S(B+A)=A*B+S(A+B)
    eq11' <- ruleSpec (Var D) prop3
    eq11' <- ruleSpec (S (Plus (Var B) (Var A))) eq11'
    eq11' <- ruleSpec (S (Plus (Var A) (Var B))) eq11'
    eq11' <- ruleGeneralize D [premise] eq11'
    eq11' <- ruleSpec (Mult (Var A) (Var B)) eq11'
    -- |- A*B+S(B+A)=A*B+S(A+B)
    eq11'' <- ruleDetachment eq11 eq11'
    -- |- SA*SB=A*B+S(A+B)
    eq12 <- ruleTransitivity eq10 eq11''
    -- |- A+SB=S(A+B)
    eq13 <- ruleSpec (Var A) ax3
    eq13 <- ruleSpec (Var B) eq13
    -- |- S(B+A)=S(A+B) -> A*B+S(B+A)=A*B+S(A+B)
    eq13' <- ruleSpec (Var D) prop3
    eq13' <- ruleSpec (Plus (Var A) (S (Var B))) eq13'
    eq13' <- ruleSpec (S (Plus (Var A) (Var B))) eq13'
    eq13' <- ruleGeneralize D [premise] eq13'
    eq13' <- ruleSpec (Mult (Var A) (Var B)) eq13'
    -- |- A*B+S(A+B)=A*B+A+SB
    eq13'' <- ruleDetachment eq13 eq13'
    eq13'' <- ruleSymmetry eq13''
    eq14 <- ruleTransitivity eq12 eq13''
    -- |- A*B+A+SB=(A*B+A)+SB
    eq15 <- ruleSpec (Var D) prop5
    eq15 <- ruleSpec (Var A) eq15
    eq15 <- ruleSpec (S (Var B)) eq15
    eq15 <- ruleGeneralize D [premise] eq15
    eq15 <- ruleSpec (Mult (Var A) (Var B)) eq15
    -- |- SA*SB=(A*B+A)+SB
    eq16 <- ruleTransitivity eq14 eq15
    -- |- A*SB=A*B+A
    eq17 <- ruleSpec (Var A) ax5
    eq17 <- ruleSpec (Var B) eq17
    -- |- A*SB=A*B+A -> SB+A*SB=SB+A*B+A
    eq17' <- ruleSpec (Var D) prop3
    eq17' <- ruleSpec (Mult (Var A) (S (Var B))) eq17'
    eq17' <- ruleSpec (Plus (Mult (Var A) (Var B)) (Var A)) eq17'
    eq17' <- ruleGeneralize D [premise] eq17'
    eq17' <- ruleSpec (S (Var B)) eq17'
    -- |- SB+A*SB=SB+A*B+A
    eq17'' <- ruleDetachment eq17 eq17'
    -- |- SB+A*B+A=(A*B+A)+SB
    eq17''' <- ruleSpec (Var D) prop4
    eq17''' <- ruleSpec (Plus (Mult (Var A) (Var B)) (Var A)) eq17'''
    eq17''' <- ruleGeneralize D [premise] eq17'''
    eq17''' <- ruleSpec (S (Var B)) eq17'''
    eq17'''' <- ruleTransitivity eq17'' eq17'''
    eq17'''' <- ruleSymmetry eq17''''
    -- |- SA*SB=SB+A*SB
    eq18 <- ruleTransitivity eq16 eq17''''
    -- |- SB+A*SB=A*SB+SB
    eq19 <- ruleSpec (Var D) prop4
    eq19 <- ruleSpec (Mult (Var A) (S (Var B))) eq19
    eq19 <- ruleGeneralize D [premise] eq19
    eq19 <- ruleSpec (S (Var B)) eq19
    ruleTransitivity eq18 eq19
  ruleGeneralize B [] imp

-- |- All A:All B:(SA*B=A*B+B)
prop7 = do
  eq1 <- join (ruleInduction <$> prop7base <*> prop7hyp)
  ruleGeneralize A [] eq1

{- Prop8 -}
-- |- A*0=0*A
prop8base = do
  prop6 <- prop6
  ax4 <- axiom4 (Var A)
  eq1 <- ruleSpec (Var A) ax4
  eq2 <- ruleSpec (Var A) prop6
  eq2 <- ruleSymmetry eq2
  ruleTransitivity eq1 eq2

-- |- All B:<A*B=B*A -> A*SB=SB*A>
prop8hyp = do
  imp <- ruleFantasy (PropVar (Eq (Mult (Var A) (Var B)) (Mult (Var B) (Var A)))) $ \premise -> do
    ax5 <- axiom5 (Var A) (Var B)
    prop3 <- prop3
    prop4 <- prop4
    prop7 <- prop7
    -- |- A*SB=A*B+A
    eq1 <- ruleSpec (Var A) ax5
    eq1 <- ruleSpec (Var B) eq1
    -- |- A*B=B*A -> A+A*B=A+B*A
    eq2 <- ruleSpec (Var A) prop3
    eq2 <- ruleSpec (Mult (Var A) (Var B)) eq2
    eq2 <- ruleSpec (Mult (Var B) (Var A)) eq2
    -- |- A+A*B=A+B*A
    eq2' <- ruleDetachment premise eq2
    -- |- A*B+A=A+A*B
    eq3 <- ruleSpec (Var D) prop4
    eq3 <- ruleSpec (Var A) eq3
    eq3 <- ruleGeneralize D [premise] eq3
    eq3 <- ruleSpec (Mult (Var A) (Var B)) eq3
    -- |- A*SB=A+A*B
    eq4 <- ruleTransitivity eq1 eq3
    -- |- A*SB=A+B*A
    eq5 <- ruleTransitivity eq4 eq2'
    -- |- A+B*A=B*A+A
    eq6 <- ruleSpec (Var D) prop4
    eq6 <- ruleSpec (Var A) eq6
    eq6 <- ruleGeneralize D [premise] eq6
    eq6 <- ruleSpec (Mult (Var B) (Var A)) eq6
    eq6 <- ruleSymmetry eq6
    -- |- A*SB=B*A+A
    eq7 <- ruleTransitivity eq5 eq6
    -- |- B*A+A=SB*A
    eq8 <- ruleSpec (Var D) prop7
    eq8 <- ruleSpec (Var A) eq8
    eq8 <- ruleGeneralize D [premise] eq8
    eq8 <- ruleSpec (Var B) eq8
    eq8 <- ruleSymmetry eq8
    ruleTransitivity eq7 eq8
  ruleGeneralize B [] imp

-- |- All A:All B:(A*B=B*A)
prop8 = do
  eq1 <- join (ruleInduction <$> prop8base <*> prop8hyp)
  ruleGeneralize A [] eq1
