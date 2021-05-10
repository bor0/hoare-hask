module ExampleTNT2 where
--TODO: Rulegeneralize u proof probaj so applyFOLRule

import Common
import ExampleCommon
import Gentzen
import PrettyPrinter
import TNT

main = do
  putStrLn "Addition"
  mapM_ (\(n,p) -> putStrLn $ show n ++ ": " ++ pr p) $ zip [1..] [prop1,prop2,prop3,prop4,prop5]
  putStrLn "Multiplication"
  mapM_ (\(n,p) -> putStrLn $ show n ++ ": " ++ pr p) $ zip [6..] [prop6,prop7,prop8]

{- Prop1 -}
-- |- 0=0+0
prop1base = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (axiom2 A) Z

-- |- All A:<A=0+A -> SA=0+SA>
prop1hyp = fromRight $ ruleGeneralize specific A Nothing
  where
  specific = ruleFantasy f (PropVar (Eq (Var A) (Plus Z (Var A))))
  f premise =
       -- |- A=0+A -> SA=S(0+A)
   let eq1 = fromRight $ ruleAddS premise
       -- |- S(0+A)=0+SA
       eq2 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (fromRight $ ruleSpec (axiom3 A B) Z) (Var A)
   in  fromRight $ ruleTransitivity eq1 eq2

-- |- All A:(A=0+A)
prop1 = fromRight $ ruleInduction prop1base prop1hyp

{- Prop2 -}
-- |- SA+0=S(A+0)
prop2base =
  -- |- SA+0=SA
  let eq1 = fromRight $ ruleSpec (axiom2 A) (S (Var A))
      -- |- A+0=A
      eq2 = fromRight $ ruleSpec (axiom2 A) (Var A)
      -- |- S(A+0)=SA
      eq2' = fromRight $ ruleAddS eq2
      -- |- SA=S(A+0)
      eq2'' = fromRight $ ruleSymmetry eq2'
  in  fromRight $ ruleTransitivity eq1 eq2''

-- |- All A:<SA+B=S(A+B) -> SA+SB=S(A+SB)>
prop2hyp = fromRight $ ruleGeneralize specific B Nothing
  where
  specific = ruleFantasy f (PropVar (Eq (Plus (S (Var A)) (Var B)) (S (Plus (Var A) (Var B)))))
  f premise =
   -- |- SA+SB=S(SA+B)
   let eq1 = fromRight $ ruleSpec (fromRight $ ruleSpec (axiom3 A B) (S (Var A))) (Var B)
       -- |- S(SA+B)=SS(A+B)
       eq2 = fromRight $ ruleAddS premise
       -- |- SA+SB=SS(A+B)
       eq3 = fromRight $ ruleTransitivity eq1 eq2
       -- |- A+SB=S(A+B)
       eq4 = fromRight $ ruleSpec (fromRight $ ruleSpec (axiom3 A B) (Var A)) (Var B)
       -- |- S(A+SB)=SS(A+B)
       eq4' = fromRight $ ruleAddS eq4
       -- |- SS(A+B)=S(A+SB)
       eq4'' = fromRight $ ruleSymmetry eq4'
   in  fromRight $ ruleTransitivity eq3 eq4''

-- |- All A:All B:(SA+B=S(A+B))
prop2 = fromRight $ ruleGeneralize (fromRight $ ruleInduction prop2base prop2hyp) A Nothing

{- Prop3 -}
-- |- B=C -> 0+B=0+C
prop3base = ruleFantasy f (PropVar (Eq (Var B) (Var C)))
  where
  f premise =
   -- |- 0+B=B
   let eq1 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec prop1 (Var B)
       -- |- C=0+C
       eq2 = fromRight $ ruleSpec prop1 (Var C)
       -- |- 0+B=C
       step1 = fromRight $ ruleTransitivity eq1 premise
   in  fromRight $ ruleTransitivity step1 eq2

-- |- All A:<<B=C -> A+B=A+C> -> B=C -> SA+B=SA+C>
prop3hyp = fromRight $ ruleGeneralize specific A Nothing
  where
  specific = ruleFantasy f (Imp (PropVar (Eq (Var B) (Var C))) (PropVar (Eq (Plus (Var A) (Var B)) (Plus (Var A) (Var C)))))
  f premise =
   let f' premise' =
        -- |- A+B=A+C
        let eq1 = fromRight $ ruleDetachment premise' premise
            -- |- S(A+B)=S(A+C)
            eq2 = fromRight $ ruleAddS eq1
            -- |- SA+B=S(A+B)
            eq3 = fromRight $ ruleSpec (fromRight $ ruleSpec prop2 (Var A)) (Var B)
            -- |- S(A+C)=SA+C
            eq4 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (fromRight $ ruleSpec prop2 (Var A)) (Var C)
            -- |- SA+B=S(A+C)
            eq5 = fromRight $ ruleTransitivity eq3 eq2
        in  fromRight $ ruleTransitivity eq5 eq4
   in  ruleFantasy f' (PropVar (Eq (Var B) (Var C)))

-- |- All A:All B:All C:<A+B=A+C -> B=C>
prop3 = fromRight $ ruleGeneralize eq3 A Nothing
  where
  -- |- A+B=A+C -> B=C
  eq1 = fromRight $ ruleSpec (fromRight $ ruleInduction prop3base prop3hyp) (Var A)
  -- |- All C:<A+B=A+C -> B=C>
  eq2 = fromRight $ ruleGeneralize eq1 C Nothing
  -- |- All B:All C:<A+B=A+C -> B=C>
  eq3 = fromRight $ ruleGeneralize eq2 B Nothing

{- Prop4 -}
-- |- A+0=0+A
prop4base = fromRight $ ruleTransitivity eq1 eq2
  where
  eq1 = fromRight $ ruleSpec (axiom2 A) (Var A)
  eq2 = fromRight $ ruleSpec prop1 (Var A)

-- |- All B:<A+B=B+A -> A+SB=SB+A>
prop4hyp = fromRight $ ruleGeneralize specific B Nothing
  where
  specific = ruleFantasy f (PropVar (Eq (Plus (Var A) (Var B)) (Plus (Var B) (Var A))))
  f premise =
   -- |- A+SB=S(A+B)
   let eq1 = fromRight $ ruleSpec (fromRight $ ruleSpec (axiom3 A B) (Var A)) (Var B)
       -- |- S(A+B)=S(B+A)
       eq2 = fromRight $ ruleAddS premise
       -- |- A+SB=S(B+A)
       eq3 = fromRight $ ruleTransitivity eq1 eq2
       -- |- SB+A=S(B+A)
       eq4 = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop2 (Var C)) (Var A)) C (Just premise)) (Var B)
       -- |- S(B+A)=SB+A
       eq4' = fromRight $ ruleSymmetry eq4
   in  fromRight $ ruleTransitivity eq3 eq4'

-- |- All A:All B:(SA+B=S(A+B))
prop4 = eq2
  where
  -- |- All B:(SA+B=S(A+B))
  eq1 = fromRight $ ruleInduction prop4base prop4hyp
  eq2 = fromRight $ ruleGeneralize eq1 A Nothing

{- Prop5 -}
-- |- A+B+0=(A+B)+0
prop5base = fromRight $ ruleTransitivity eq3 eq4
  where
  -- |- B+0=B
  eq1 = fromRight $ ruleSpec (axiom2 B) (Var B)
  -- |- B+0=B -> A+B+0=A+B
  eq2 = fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 (Var A)) (Plus (Var B) Z)) (Var B)
  -- |- A+B+0=A+B
  eq3 = fromRight $ ruleDetachment eq1 eq2
  -- |- A+B=(A+B)+0
  eq4 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (axiom2 A) (Plus (Var A) (Var B))
  -- |- A+B+0=(A+B)+0
  eq5 = fromRight $ ruleTransitivity eq3 eq4

-- |- All C:<A+B+C=(A+B)+C -> A+B+SC=(A+B)+SC>
prop5hyp = fromRight $ ruleGeneralize specific C Nothing
  where
  specific = ruleFantasy f (PropVar (Eq (Plus (Var A) (Plus (Var B) (Var C))) (Plus (Plus (Var A) (Var B)) (Var C))))
  f premise =
   -- |- B+SC=S(B+C)
   let eq1 = fromRight $ ruleSpec (applyFOLRule [GoRight] (\f -> fromRight $ ruleSpec f (Var C)) (axiom3 A B)) (Var B)
       -- |- B=S(D+C) -> A+B=A+S(D+C)
       eq2 = fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 (Var A)) (Var E)) (S (Plus (Var D) (Var C)))
       -- |- B+SC=S(D+C) -> A+B+SC=A+S(D+C)
       eq2' = fromRight $ ruleSpec (fromRight $ ruleGeneralize eq2 E (Just premise)) (Plus (Var B) (S (Var C)))
       -- |- B+SC=S(B+C) -> A+B+SC=A+S(B+C)
       eq2'' = fromRight $ ruleSpec (fromRight $ ruleGeneralize eq2' D (Just premise)) (Var B)
       -- |- A+B+SC=A+S(B+C)
       eq3 = fromRight $ ruleDetachment eq1 eq2''
       -- |- A+S(B+C)=S(A+B+C)
       eq4 = fromRight $ ruleSpec (fromRight $ ruleSpec (axiom3 A B) (Var A)) (Plus (Var B) (Var C))
       -- |- A+B+SC=S(A+B+C)
       eq5 = fromRight $ ruleTransitivity eq3 eq4
       -- |- S(A+B+C)=S((A+B)+C)
       eq6 = fromRight $ ruleAddS premise
       -- |- A+B+SC=S((A+B)+C)
       eq7 = fromRight $ ruleTransitivity eq5 eq6
       -- |- S((A+B)+C)=(A+B)+SC
       eq8 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (applyFOLRule [GoRight] (\f -> fromRight $ ruleSpec f (Var C)) (axiom3 A B)) (Plus (Var A) (Var B))
   in  fromRight $ ruleTransitivity eq7 eq8

-- |- All A:All B:All C:(A+B+C=(A+B)+C)
prop5 = fromRight $ ruleGeneralize eq2 A Nothing
  where
  -- |- All C:(A+B+C=(A+B)+C
  eq1 = fromRight $ ruleInduction prop5base prop5hyp
  -- |- All B:All C:(A+B+C=(A+B)+C)
  eq2 = fromRight $ ruleGeneralize eq1 B Nothing

{- Prop6 -}
-- |- 0*0=0
prop6base = fromRight $ ruleSpec (axiom4 A) Z

-- |- All A:<0*A=0 -> 0*SA=0>
prop6hyp = fromRight $ ruleGeneralize specific A Nothing
  where
  specific = ruleFantasy f (PropVar (Eq (Mult Z (Var A)) Z))
  f premise =
   -- |- All B:(0*SB=0*B+0)
   let eq1 = fromRight $ ruleSpec (axiom5 A B) Z
       -- |- 0*SA=0*A+0
       eq2 = fromRight $ ruleSpec eq1 (Var A)
       -- |- 0*A+0=0*A
       eq3 = fromRight $ ruleSpec (axiom2 A) (Mult Z (Var A))
       -- |- 0*SA=0*A
       eq4 = fromRight $ ruleTransitivity eq2 eq3
   in  fromRight $ ruleTransitivity eq4 premise

-- |- All A:(0*A=0)
prop6 = fromRight $ ruleInduction prop6base prop6hyp

{- Prop7 -}
-- |- SA*0=A*0+0
prop7base =
  -- |- SA*0=0
  let eq1 = fromRight $ ruleSpec (axiom4 A) (S (Var A))
      -- |- 0=0+0
      eq2 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (axiom2 A) Z
      -- |- SA*0=0+0
      eq2' = fromRight $ ruleTransitivity eq1 eq2
      -- |- A*0=0
      eq3 = fromRight $ ruleSpec (axiom4 A) (Var A)
      eq4 = fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 Z) (Mult (Var A) Z)) Z
      -- |- 0+0=0+A*0
      eq4' = fromRight $ ruleSymmetry $ fromRight $ ruleDetachment eq3 eq4
      -- |- SA*0=0+0
      eq5 = fromRight $ ruleTransitivity eq1 eq2
      -- |- SA*0=0+A*0
      eq6 = fromRight $ ruleTransitivity eq5 eq4'
      -- |- 0+A*0=A*0+
      eq7 = fromRight $ ruleSpec (fromRight $ ruleSpec prop4 Z) (Mult (Var A) Z)
  in  fromRight $ ruleTransitivity eq6 eq7

-- |- All B:<SA*B=A*B+B -> SA*SB=A*SB+SB>
prop7hyp = fromRight $ ruleGeneralize specific B Nothing
  where
  specific = ruleFantasy f (PropVar (Eq (Mult (S (Var A)) (Var B)) (Plus (Mult (Var A) (Var B)) (Var B))))
  f premise = -- | SA*B=A*B+B
   -- |- SA*SB=SA*B+SA
   let eq1 = fromRight $ ruleSpec (fromRight $ ruleSpec (axiom5 A B) (S (Var A))) (Var B)
       -- |- SA*B+SA=SA+SA*B
       eq2 = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop4 (Var D)) (S (Var A))) D (Just premise)) (Mult (S (Var A)) (Var B))
       eq2' = fromRight $ ruleTransitivity eq1 eq2
       eq3 = fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 (S (Var A))) (Mult (S (Var A)) (Var B))) (Plus (Mult (Var A) (Var B)) (Var B))
       eq3' = fromRight $ ruleDetachment premise eq3
       -- |- SA*SB=SA+A*B+B
       eq4 = fromRight $ ruleTransitivity eq2' eq3'
       -- |- SA+A*B+B=(A*B+B)+SA
       eq5 = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop4 (Var D)) (Plus (Mult (Var A) (Var B)) (Var B))) D (Just premise)) (S (Var A))
       -- |- SA*SB=(A*B+B)+SA
       eq6 = fromRight $ ruleTransitivity eq4 eq5
       -- |- A*B+B+SA=(A*B+B)+SA
       eq7 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (fromRight $ ruleSpec (applyFOLRule [GoRight] (\f -> fromRight $ ruleSpec f (Var B)) prop5) (Mult (Var A) (Var B))) (S (Var A))
       -- |- SA*SB=A*B+B+SA
       eq8 = fromRight $ ruleTransitivity eq6 eq7
       -- |- B+SA=S(B+A)
       eq9 = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec (axiom3 A B) (Var D)) (Var A)) D (Just premise)) (Var B)
       -- |- B+SA=S(B+A) -> SA+B+SA=SA+S(B+A)
       eq9' = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 (Var D)) (Plus (Var B) (S (Var A)))) (S (Plus (Var B) (Var A)))) D (Just premise)) (Mult (Var A) (Var B))
       -- |- A*B+B+SA=A*B+S(B+A)
       eq9'' = fromRight $ ruleDetachment eq9 eq9'
       -- |- SA*SB=A*B+S(B+A)
       eq10 = fromRight $ ruleTransitivity eq8 eq9''
       -- |- S(B+A)=S(A+B)
       eq11 = fromRight $ ruleAddS $ fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop4 (Var D)) (Var A)) D (Just premise)) (Var B)
       -- |- S(B+A)=S(A+B) -> A*B+S(B+A)=A*B+S(A+B)
       eq11' = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 (Var D)) (S (Plus (Var B) (Var A)))) (S (Plus (Var A) (Var B)))) D (Just premise)) (Mult (Var A) (Var B))
       -- |- A*B+S(B+A)=A*B+S(A+B)
       eq11'' = fromRight $ ruleDetachment eq11 eq11'
       -- |- SA*SB=A*B+S(A+B)
       eq12 = fromRight $ ruleTransitivity eq10 eq11''
       -- |- A+SB=S(A+B)
       eq13 = fromRight $ ruleSpec (fromRight $ ruleSpec (axiom3 A B) (Var A)) (Var B)
       -- |- S(B+A)=S(A+B) -> A*B+S(B+A)=A*B+S(A+B)
       eq13' = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 (Var D)) (Plus (Var A) (S (Var B)))) (S (Plus (Var A) (Var B)))) D (Just premise)) (Mult (Var A) (Var B))
       -- |- A*B+S(A+B)=A*B+A+SB
       eq13'' = fromRight $ ruleSymmetry $ fromRight $ ruleDetachment eq13 eq13'
       eq14 = fromRight $ ruleTransitivity eq12 eq13''
       -- |- A*B+A+SB=(A*B+A)+SB
       eq15 = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop5 (Var D)) (Var A)) (S (Var B))) D (Just premise)) (Mult (Var A) (Var B))
       -- |- SA*SB=(A*B+A)+SB
       eq16 = fromRight $ ruleTransitivity eq14 eq15
       -- |- A*SB=A*B+A
       eq17 = fromRight $ ruleSpec (fromRight $ ruleSpec (axiom5 A B) (Var A)) (Var B)
       -- |- A*SB=A*B+A -> SB+A*SB=SB+A*B+A
       eq17' = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 (Var D)) (Mult (Var A) (S (Var B)))) (Plus (Mult (Var A) (Var B)) (Var A))) D (Just premise)) (S (Var B))
       -- |- SB+A*SB=SB+A*B+A
       eq17'' = fromRight $ ruleDetachment eq17 eq17'
       -- |- SB+A*B+A=(A*B+A)+SB
       eq17''' = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop4 (Var D)) (Plus (Mult (Var A) (Var B)) (Var A))) D (Just premise)) (S (Var B))
       eq17'''' = fromRight $ ruleSymmetry $ fromRight $ ruleTransitivity eq17'' eq17'''
       -- |- SA*SB=SB+A*SB
       eq18 = fromRight $ ruleTransitivity eq16 eq17''''
       -- |- SB+A*SB=A*SB+SB
       eq19 = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop4 (Var D)) (Mult (Var A) (S (Var B)))) D (Just premise)) (S (Var B))
   in  fromRight $ ruleTransitivity eq18 eq19

-- |- All A:All B:(SA*B=A*B+B)
prop7 = fromRight $ ruleGeneralize (fromRight $ ruleInduction prop7base prop7hyp) A Nothing

{- Prop8 -}
-- |- A*0=0*A
prop8base = fromRight $ ruleTransitivity eq1 eq2
  where
  eq1 = fromRight $ ruleSpec (axiom4 A) (Var A)
  eq2 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec prop6 (Var A)

-- |- All B:<A*B=B*A -> A*SB=SB*A>
prop8hyp = fromRight $ ruleGeneralize specific B Nothing
  where
  specific = ruleFantasy f (PropVar (Eq (Mult (Var A) (Var B)) (Mult (Var B) (Var A))))
  f premise =
   -- |- A*SB=A*B+A
   let eq1 = fromRight $ ruleSpec (fromRight $ ruleSpec (axiom5 A B) (Var A)) (Var B)
       -- |- A*B=B*A -> A+A*B=A+B*A
       eq2 = fromRight $ ruleSpec (fromRight $ ruleSpec (fromRight $ ruleSpec prop3 (Var A)) (Mult (Var A) (Var B))) (Mult (Var B) (Var A))
       -- |- A+A*B=A+B*A
       eq2' = fromRight $ ruleDetachment premise eq2
       -- |- A*B+A=A+A*B
       eq3 = fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop4 (Var D)) (Var A)) D (Just premise)) (Mult (Var A) (Var B))
       -- |- A*SB=A+A*B
       eq4 = fromRight $ ruleTransitivity eq1 eq3
       -- |- A*SB=A+B*A
       eq5 = fromRight $ ruleTransitivity eq4 eq2'
       -- |- A+B*A=B*A+A
       eq6 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop4 (Var D)) (Var A)) D (Just premise)) (Mult (Var B) (Var A))
       -- |- A*SB=B*A+A
       eq7 = fromRight $ ruleTransitivity eq5 eq6
       -- |- B*A+A=SB*A
       eq8 = fromRight $ ruleSymmetry $ fromRight $ ruleSpec (fromRight $ ruleGeneralize (fromRight $ ruleSpec (fromRight $ ruleSpec prop7 (Var D)) (Var A)) D (Just premise)) (Var B)
   in  fromRight $ ruleTransitivity eq7 eq8

-- |- All A:All B:(A*B=B*A)
prop8 = eq2
  where
  eq1 = fromRight $ ruleInduction prop8base prop8hyp
  eq2 = fromRight $ ruleGeneralize eq1 A Nothing
