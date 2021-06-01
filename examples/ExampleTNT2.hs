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
  putStrLn $ pr $ let formula = Proof $ And (PropVar $ Eq (Var A) (Var B)) (PropVar $ Exists B (PropVar (Eq (Var B) (Var C)))) in applyFOLRule [GoLeft] (\prfAeqB -> applyFOLRule [GoRight,GoLeft] (ruleTransitivity prfAeqB) formula []) formula []
  putStrLn $ pr $ let formula = Proof $ And (PropVar $ Eq (Var A) (Var B)) (PropVar $ Exists B (PropVar (Eq (Var B) (Var C)))) in applyFOLRule [GoLeft] (\prfAeqB -> applyFOLRule [GoRight,GoLeft] (ruleTransitivity prfAeqB) formula [prfAeqB]) formula []

{- Prop1 -}
-- |- 0=0+0
prop1base = do
  step1 <- axiom2 (Var A)
  step2 <- ruleSpec step1 Z
  ruleSymmetry step2

-- |- All A:<A=0+A -> SA=0+SA>
prop1hyp = do
  imp <- ruleFantasy (PropVar (Eq (Var A) (Plus Z (Var A)))) $ \premise -> do
    -- |- A=0+A -> SA=S(0+A)
    eq1 <- ruleAddS premise
    step1 <- axiom3 (Var A) (Var B)
    step2 <- ruleSpec step1 Z
    step3 <- ruleSpec step2 (Var A)
    -- |- S(0+A)=0+SA
    eq2 <- ruleSymmetry step3
    ruleTransitivity eq1 eq2
  ruleGeneralize imp A []

-- |- All A:(A=0+A)
prop1 = join $ ruleInduction <$> prop1base <*> prop1hyp

{- Prop2 -}
-- |- SA+0=S(A+0)
prop2base = do
  -- |- SA+0=SA
  step1 <- axiom2 (Var A)
  eq1 <- ruleSpec step1 (S (Var A))
  -- |- A+0=A
  eq2 <- ruleSpec step1 (Var A)
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
    eq1 <- ruleSpec step1 (S (Var A))
    eq1 <- ruleSpec eq1 (Var B)
    -- |- S(SA+B)=SS(A+B)
    eq2 <- ruleAddS premise
    -- |- SA+SB=SS(A+B)
    eq3 <- ruleTransitivity eq1 eq2
    -- |- A+SB=S(A+B)
    eq4 <- ruleSpec step1 (Var A)
    eq4 <- ruleSpec eq4 (Var B)
    -- |- S(A+SB)=SS(A+B)
    eq4' <- ruleAddS eq4
    -- |- SS(A+B)=S(A+SB)
    eq4'' <- ruleSymmetry eq4'
    ruleTransitivity eq3 eq4''
  ruleGeneralize imp B []

-- |- All A:All B:(SA+B=S(A+B))
prop2 = join (ruleInduction <$> prop2base <*> prop2hyp) >>= \prf -> ruleGeneralize prf A []

{- Prop3 -}
-- |- B=C -> 0+B=0+C
prop3base = ruleFantasy (PropVar (Eq (Var B) (Var C))) $ \premise -> do
  prop1 <- prop1
  step1 <- ruleSpec prop1 (Var B)
  -- |- 0+B=B
  eq1 <- ruleSymmetry step1
  -- |- C=0+C
  eq2 <- ruleSpec prop1 (Var C)
  -- |- 0+B=C
  eq3 <- ruleTransitivity eq1 premise
  ruleTransitivity eq3 eq2

-- |- All A:<<B=C -> A+B=A+C> -> B=C -> SA+B=SA+C>
prop3hyp = do
  imp <- ruleFantasy (Imp (PropVar (Eq (Var B) (Var C))) (PropVar (Eq (Plus (Var A) (Var B)) (Plus (Var A) (Var C))))) $ \premise -> do
   ruleFantasy (PropVar (Eq (Var B) (Var C))) $ \premise2 -> do
     prop2 <- prop2
     prop2 <- ruleSpec prop2 (Var A)
     -- |- A+B=A+C
     eq1 <- ruleDetachment premise2 premise
     -- |- S(A+B)=S(A+C)
     eq2 <- ruleAddS eq1
     -- |- SA+B=S(A+B)
     eq3 <- ruleSpec prop2 (Var B)
     eq3' <- ruleSpec prop2 (Var C)
     -- |- S(A+C)=SA+C
     eq4 <- ruleSymmetry eq3'
     -- |- SA+B=S(A+C)
     eq5 <- ruleTransitivity eq3 eq2
     ruleTransitivity eq5 eq4
  ruleGeneralize imp A []

-- |- All A:All B:All C:<B=C -> A+B=A+C>
prop3 = do
  eq1 <- join (ruleInduction <$> prop3base <*> prop3hyp)
  -- |- B=C -> A+B=A+C
  eq1 <- ruleSpec eq1 (Var A)
  -- |- All C:<B=C -> A+B=A+C>
  eq2 <- ruleGeneralize eq1 C []
  -- |- All B:All C:<B=C -> A+B=A+C>
  eq3 <- ruleGeneralize eq2 B []
  ruleGeneralize eq3 A []

{- Prop4 -}
-- |- A+0=0+A
prop4base = do
  ax2 <- axiom2 (Var A)
  prop1 <- prop1
  eq1 <- ruleSpec ax2 (Var A)
  eq2 <- ruleSpec prop1 (Var A)
  ruleTransitivity eq1 eq2

-- |- All B:<A+B=B+A -> A+SB=SB+A>
prop4hyp = do
  imp <- ruleFantasy (PropVar (Eq (Plus (Var A) (Var B)) (Plus (Var B) (Var A)))) $ \premise -> do
    ax3 <- axiom3 (Var A) (Var B)
    step1 <- ruleSpec ax3 (Var A)
    prop2 <- prop2
    -- |- A+SB=S(A+B)
    eq1 <- ruleSpec step1 (Var B)
    -- |- S(A+B)=S(B+A)
    eq2 <- ruleAddS premise
    -- |- A+SB=S(B+A)
    eq3 <- ruleTransitivity eq1 eq2
    step2 <- ruleSpec prop2 (Var C)
    step2 <- ruleSpec step2 (Var A)
    step2 <- ruleGeneralize step2 C [premise]
    -- |- SB+A=S(B+A)
    eq4 <- ruleSpec step2 (Var B)
    -- |- S(B+A)=SB+A
    eq4' <- ruleSymmetry eq4
    ruleTransitivity eq3 eq4'
  ruleGeneralize imp B []

-- |- All A:All B:(A+B=B+A)
prop4 = do
  -- |- All B:(A+B=B+A)
  eq1 <- join (ruleInduction <$> prop4base <*> prop4hyp)
  ruleGeneralize eq1 A []

{- Prop5 -}
-- |- A+B+0=(A+B)+0
prop5base = do
  ax2 <- axiom2 (Var A)
  prop3 <- prop3
  -- |- B+0=B
  eq1 <- ruleSpec ax2 (Var B)
  -- |- B+0=B -> A+B+0=A+B
  eq2 <- ruleSpec prop3 (Var A)
  eq2 <- ruleSpec eq2 (Plus (Var B) Z)
  eq2 <- ruleSpec eq2 (Var B)
  -- |- A+B+0=A+B
  eq3 <- ruleDetachment eq1 eq2
  -- |- A+B=(A+B)+0
  eq4 <- ruleSpec ax2 (Plus (Var A) (Var B))
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
    eq1 <- applyFOLRule [GoRight] (\f -> ruleSpec f (Var C)) ax3 []
    eq1 <- ruleSpec eq1 (Var B)
    -- |- B=S(D+C) -> A+B=A+S(D+C)
    eq2 <- ruleSpec prop3 (Var A)
    eq2 <- ruleSpec eq2 (Var E)
    eq2 <- ruleSpec eq2 (S (Plus (Var D) (Var C)))
    -- |- B+SC=S(D+C) -> A+B+SC=A+S(D+C)
    eq2' <- ruleGeneralize eq2 E [premise]
    eq2' <- ruleSpec eq2' (Plus (Var B) (S (Var C)))
    -- |- B+SC=S(B+C) -> A+B+SC=A+S(B+C)
    eq2'' <- ruleGeneralize eq2' D [premise]
    eq2'' <- ruleSpec eq2'' (Var B)
    -- |- A+B+SC=A+S(B+C)
    eq3 <- ruleDetachment eq1 eq2''
    -- |- A+S(B+C)=S(A+B+C)
    eq4 <- ruleSpec ax3 (Var A)
    eq4 <- ruleSpec eq4 (Plus (Var B) (Var C))
    -- |- A+B+SC=S(A+B+C)
    eq5 <- ruleTransitivity eq3 eq4
    -- |- S(A+B+C)=S((A+B)+C)
    eq6 <- ruleAddS premise
    -- |- A+B+SC=S((A+B)+C)
    eq7 <- ruleTransitivity eq5 eq6
    -- |- S((A+B)+C)=(A+B)+SC
    eq8 <- applyFOLRule [GoRight] (\f -> ruleSpec f (Var C)) ax3 []
    eq8 <- ruleSpec eq8 (Plus (Var A) (Var B))
    eq8 <- ruleSymmetry eq8
    ruleTransitivity eq7 eq8
  ruleGeneralize imp C []

-- |- All A:All B:All C:(A+B+C=(A+B)+C)
prop5 = do
  -- |- All C:(A+B+C=(A+B)+C
  eq1 <- join (ruleInduction <$> prop5base <*> prop5hyp)
  -- |- All B:All C:(A+B+C=(A+B)+C)
  eq2 <- ruleGeneralize eq1 B []
  ruleGeneralize eq2 A []

{- Prop6 -}
-- |- 0*0=0
prop6base = do
  ax4 <- axiom4 (Var A)
  ruleSpec ax4 Z

-- |- All A:<0*A=0 -> 0*SA=0>
prop6hyp = do
  imp <- ruleFantasy (PropVar (Eq (Mult Z (Var A)) Z)) $ \premise -> do
    ax5 <- axiom5 (Var A) (Var B)
    ax2 <- axiom2 (Var A)
    eq1 <- ruleSpec ax5 Z
    -- |- 0*SA=0*A+0
    eq2 <- ruleSpec eq1 (Var A)
    -- |- 0*A+0=0*A
    eq3 <- ruleSpec ax2 (Mult Z (Var A))
    -- |- 0*SA=0*A
    eq4 <- ruleTransitivity eq2 eq3
    ruleTransitivity eq4 premise
  ruleGeneralize imp A []

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
  eq1 <- ruleSpec ax4 (S (Var A))
  -- |- 0=0+0
  eq2 <- ruleSpec ax2 Z
  eq2 <- ruleSymmetry eq2
  -- |- SA*0=0+0
  eq2' <- ruleTransitivity eq1 eq2
  -- |- A*0=0
  eq3 <- ruleSpec ax4 (Var A)
  eq4 <- ruleSpec prop3 Z
  eq4 <- ruleSpec eq4 (Mult (Var A) Z)
  eq4 <- ruleSpec eq4 Z
  -- |- 0+0=0+A*0
  eq4' <- ruleDetachment eq3 eq4
  eq4' <- ruleSymmetry eq4'
  -- |- SA*0=0+0
  eq5 <- ruleTransitivity eq1 eq2
  -- |- SA*0=0+A*0
  eq6 <- ruleTransitivity eq5 eq4'
  -- |- 0+A*0=A*0+0
  eq7 <- ruleSpec prop4 Z
  eq7 <- ruleSpec eq7 (Mult (Var A) Z)
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
    eq1 <- ruleSpec ax5 (S (Var A))
    eq1 <- ruleSpec eq1 (Var B)
    -- |- SA*B+SA=SA+SA*B
    eq2 <- ruleSpec prop4 (Var D)
    eq2 <- ruleSpec eq2 (S (Var A))
    eq2 <- ruleGeneralize eq2 D [premise]
    eq2 <- ruleSpec eq2 (Mult (S (Var A)) (Var B))
    eq2' <- ruleTransitivity eq1 eq2
    eq3 <- ruleSpec prop3 (S (Var A))
    eq3 <- ruleSpec eq3 (Mult (S (Var A)) (Var B))
    eq3 <- ruleSpec eq3 (Plus (Mult (Var A) (Var B)) (Var B))
    eq3' <- ruleDetachment premise eq3
    -- |- SA*SB=SA+A*B+B
    eq4 <- ruleTransitivity eq2' eq3'
    -- |- SA+A*B+B=(A*B+B)+SA
    eq5 <- ruleSpec prop4 (Var D)
    eq5 <- ruleSpec eq5 (Plus (Mult (Var A) (Var B)) (Var B))
    eq5 <- ruleGeneralize eq5 D [premise]
    eq5 <- ruleSpec eq5 (S (Var A))
    -- |- SA*SB=(A*B+B)+SA
    eq6 <- ruleTransitivity eq4 eq5
    -- |- A*B+B+SA=(A*B+B)+SA
    eq7 <- applyFOLRule [GoRight] (\f -> ruleSpec f (Var B)) prop5 []
    eq7 <- ruleSpec eq7 (Mult (Var A) (Var B))
    eq7 <- ruleSpec eq7 (S (Var A))
    eq7 <- ruleSymmetry eq7
    -- |- SA*SB=A*B+B+SA
    eq8 <- ruleTransitivity eq6 eq7
    -- |- B+SA=S(B+A)
    eq9 <- ruleSpec ax3 (Var D)
    eq9 <- ruleSpec eq9 (Var A)
    eq9 <- ruleGeneralize eq9 D [premise]
    eq9 <- ruleSpec eq9 (Var B)
    -- |- B+SA=S(B+A) -> SA+B+SA=SA+S(B+A)
    eq9' <- ruleSpec prop3 (Var D)
    eq9' <- ruleSpec eq9' (Plus (Var B) (S (Var A)))
    eq9' <- ruleSpec eq9' (S (Plus (Var B) (Var A)))
    eq9' <- ruleGeneralize eq9' D [premise]
    eq9' <- ruleSpec eq9' (Mult (Var A) (Var B))
    -- |- A*B+B+SA=A*B+S(B+A)
    eq9'' <- ruleDetachment eq9 eq9'
    -- |- SA*SB=A*B+S(B+A)
    eq10 <- ruleTransitivity eq8 eq9''
    -- |- S(B+A)=S(A+B)
    eq11 <- ruleSpec prop4 (Var D)
    eq11 <- ruleSpec eq11 (Var A)
    eq11 <- ruleGeneralize eq11 D [premise]
    eq11 <- ruleSpec eq11 (Var B)
    eq11 <- ruleAddS eq11
    -- |- S(B+A)=S(A+B) -> A*B+S(B+A)=A*B+S(A+B)
    eq11' <- ruleSpec prop3 (Var D)
    eq11' <- ruleSpec eq11' (S (Plus (Var B) (Var A)))
    eq11' <- ruleSpec eq11' (S (Plus (Var A) (Var B)))
    eq11' <- ruleGeneralize eq11' D [premise]
    eq11' <- ruleSpec eq11' (Mult (Var A) (Var B))
    -- |- A*B+S(B+A)=A*B+S(A+B)
    eq11'' <- ruleDetachment eq11 eq11'
    -- |- SA*SB=A*B+S(A+B)
    eq12 <- ruleTransitivity eq10 eq11''
    -- |- A+SB=S(A+B)
    eq13 <- ruleSpec ax3 (Var A)
    eq13 <- ruleSpec eq13 (Var B)
    -- |- S(B+A)=S(A+B) -> A*B+S(B+A)=A*B+S(A+B)
    eq13' <- ruleSpec prop3 (Var D)
    eq13' <- ruleSpec eq13' (Plus (Var A) (S (Var B)))
    eq13' <- ruleSpec eq13' (S (Plus (Var A) (Var B)))
    eq13' <- ruleGeneralize eq13' D [premise]
    eq13' <- ruleSpec eq13' (Mult (Var A) (Var B))
    -- |- A*B+S(A+B)=A*B+A+SB
    eq13'' <- ruleDetachment eq13 eq13'
    eq13'' <- ruleSymmetry eq13''
    eq14 <- ruleTransitivity eq12 eq13''
    -- |- A*B+A+SB=(A*B+A)+SB
    eq15 <- ruleSpec prop5 (Var D)
    eq15 <- ruleSpec eq15 (Var A)
    eq15 <- ruleSpec eq15 (S (Var B))
    eq15 <- ruleGeneralize eq15 D [premise]
    eq15 <- ruleSpec eq15 (Mult (Var A) (Var B))
    -- |- SA*SB=(A*B+A)+SB
    eq16 <- ruleTransitivity eq14 eq15
    -- |- A*SB=A*B+A
    eq17 <- ruleSpec ax5 (Var A)
    eq17 <- ruleSpec eq17 (Var B)
    -- |- A*SB=A*B+A -> SB+A*SB=SB+A*B+A
    eq17' <- ruleSpec prop3 (Var D)
    eq17' <- ruleSpec eq17' (Mult (Var A) (S (Var B)))
    eq17' <- ruleSpec eq17' (Plus (Mult (Var A) (Var B)) (Var A))
    eq17' <- ruleGeneralize eq17' D [premise]
    eq17' <- ruleSpec eq17' (S (Var B))
    -- |- SB+A*SB=SB+A*B+A
    eq17'' <- ruleDetachment eq17 eq17'
    -- |- SB+A*B+A=(A*B+A)+SB
    eq17''' <- ruleSpec prop4 (Var D)
    eq17''' <- ruleSpec eq17''' (Plus (Mult (Var A) (Var B)) (Var A))
    eq17''' <- ruleGeneralize eq17''' D [premise]
    eq17''' <- ruleSpec eq17''' (S (Var B))
    eq17'''' <- ruleTransitivity eq17'' eq17'''
    eq17'''' <- ruleSymmetry eq17''''
    -- |- SA*SB=SB+A*SB
    eq18 <- ruleTransitivity eq16 eq17''''
    -- |- SB+A*SB=A*SB+SB
    eq19 <- ruleSpec prop4 (Var D)
    eq19 <- ruleSpec eq19 (Mult (Var A) (S (Var B)))
    eq19 <- ruleGeneralize eq19 D [premise]
    eq19 <- ruleSpec eq19 (S (Var B))
    ruleTransitivity eq18 eq19
  ruleGeneralize imp B []

-- |- All A:All B:(SA*B=A*B+B)
prop7 = do
  eq1 <- join (ruleInduction <$> prop7base <*> prop7hyp)
  ruleGeneralize eq1 A []

{- Prop8 -}
-- |- A*0=0*A
prop8base = do
  prop6 <- prop6
  ax4 <- axiom4 (Var A)
  eq1 <- ruleSpec ax4 (Var A)
  eq2 <- ruleSpec prop6 (Var A)
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
    eq1 <- ruleSpec ax5 (Var A)
    eq1 <- ruleSpec eq1 (Var B)
    -- |- A*B=B*A -> A+A*B=A+B*A
    eq2 <- ruleSpec prop3 (Var A)
    eq2 <- ruleSpec eq2 (Mult (Var A) (Var B))
    eq2 <- ruleSpec eq2 (Mult (Var B) (Var A))
    -- |- A+A*B=A+B*A
    eq2' <- ruleDetachment premise eq2
    -- |- A*B+A=A+A*B
    eq3 <- ruleSpec prop4 (Var D)
    eq3 <- ruleSpec eq3 (Var A)
    eq3 <- ruleGeneralize eq3 D [premise]
    eq3 <- ruleSpec eq3 (Mult (Var A) (Var B))
    -- |- A*SB=A+A*B
    eq4 <- ruleTransitivity eq1 eq3
    -- |- A*SB=A+B*A
    eq5 <- ruleTransitivity eq4 eq2'
    -- |- A+B*A=B*A+A
    eq6 <- ruleSpec prop4 (Var D)
    eq6 <- ruleSpec eq6 (Var A)
    eq6 <- ruleGeneralize eq6 D [premise]
    eq6 <- ruleSpec eq6 (Mult (Var B) (Var A))
    eq6 <- ruleSymmetry eq6
    -- |- A*SB=B*A+A
    eq7 <- ruleTransitivity eq5 eq6
    -- |- B*A+A=SB*A
    eq8 <- ruleSpec prop7 (Var D)
    eq8 <- ruleSpec eq8 (Var A)
    eq8 <- ruleGeneralize eq8 D [premise]
    eq8 <- ruleSpec eq8 (Var B)
    eq8 <- ruleSymmetry eq8
    ruleTransitivity eq7 eq8
  ruleGeneralize imp B []

-- |- All A:All B:(A*B=B*A)
prop8 = do
  eq1 <- join (ruleInduction <$> prop8base <*> prop8hyp)
  ruleGeneralize eq1 A []
