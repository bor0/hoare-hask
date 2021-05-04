module ExampleGentzen where

import Common
import ExampleCommon
import Gentzen
import PrettyPrinter
import TNT

-- Helpers
bottom x = And x (Not x)
-- |- <A> \/ <~A>
exclMiddle x = ruleSwitcheroo $ ruleFantasy id (Not x)

-- Example proofs for exercises taken from http://incredible.pm/

-- | Session 1
-- |- <~<a> -> <b>> -> <<a> /\ <~b>>
s1lemma1 a b = ruleFantasy f (Not (Imp a b))
  where
  f premise =
   let step1 = applyPropRule [GoLeft,GoLeft] ruleDoubleTildeIntro premise
       step2 = ruleDeMorgan $ applyPropRule [GoLeft] (fromRight . ruleSwitcheroo) step1
       in applyPropRule [GoLeft] (fromRight . ruleDoubleTildeElim) $ fromRight step2

-- |- <A> -> <A>
s1prf1 = ruleFantasy id (PropVar (Var A))
-- |- <<A> /\ <B>> -> <A>
s1prf2 = ruleFantasy (fromRight . ruleSepL) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <B>
s1prf3 = ruleFantasy (fromRight . ruleSepR) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <A>
s1prf3_2 = ruleFantasy (fromRight . ruleSepL) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <<A> /\ <B>>
s1prf4 = ruleFantasy id (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <A> -> <<A> /\ <A>>
s1prf5 = ruleFantasy (\prfA -> ruleJoin prfA prfA) (PropVar (Var A))
-- |- <<A> /\ <B>> -> <A>
s1prf6 = ruleFantasy (\prfAB -> fromRight $ ruleSepL prfAB) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <A>
s1prf7 = ruleFantasy (fromRight . ruleSepL) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <B>
s1prf7_2 = ruleFantasy (fromRight . ruleSepR) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <<A> /\ <B>>
s1prf8 = ruleFantasy id (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <<B> /\ <A>>
s1prf9 = ruleFantasy (\prfAB -> ruleJoin (fromRight $ ruleSepR prfAB) (fromRight $ ruleSepL prfAB)) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<<A> /\ <B>> /\ <C>> -> <A>
s1prf10 = ruleFantasy (\prfABC -> fromRight $ ruleSepL $ fromRight $ ruleSepL prfABC) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> /\ <B>> /\ <C>> -> <B>
s1prf10_2 = ruleFantasy (\prfABC -> fromRight $ ruleSepR $ fromRight $ ruleSepL prfABC) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> /\ <B>> /\ <C>> -> <C>
s1prf10_3 = ruleFantasy (\prfABC -> fromRight $ ruleSepR prfABC) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> /\ <B>> /\ <C>> -> <<A> /\ <C>>
s1prf11 = ruleFantasy (\prfABC -> ruleJoin (fromRight $ ruleSepL $ fromRight $ ruleSepL prfABC) (fromRight $ ruleSepR prfABC)) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> /\ <B>> /\ <C>> -> <<A> /\ <<B> /\ <C>>>
s1prf12 = ruleFantasy (\prfABC -> ruleJoin (fromRight $ ruleSepL $ fromRight $ ruleSepL prfABC) (ruleJoin (fromRight $ ruleSepR $ fromRight $ ruleSepL prfABC) (fromRight $ ruleSepR prfABC))) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))

-- | Session 2
-- |- <<A> /\ <<A> -> <B>>> -> <B>
s2prf1 = ruleFantasy (\prfAAtoB -> fromRight $ ruleDetachment (fromRight $ ruleSepL prfAAtoB) (fromRight $ ruleSepR prfAAtoB)) (And (PropVar (Var A)) (Imp (PropVar (Var A)) (PropVar (Var B))))
-- |- <<A> /\ <<<A> -> <B>> /\ <<B> -> <C>>>> -> <C>
s2prf2 = ruleFantasy (\prfAAtoBAtoC -> let prfA = fromRight (ruleSepL prfAAtoBAtoC) in let prfAtoB = fromRight (ruleSepL $ fromRight $ ruleSepR prfAAtoBAtoC) in let prfBtoC = fromRight (ruleSepR $ fromRight $ ruleSepR prfAAtoBAtoC) in fromRight $ ruleDetachment (fromRight $ ruleDetachment prfA prfAtoB) prfBtoC) (And (PropVar (Var A)) (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var B)) (PropVar (Var C)))))
-- |- <<A> /\ <<<<A> -> <B>> /\ <<B> -> <D>>> /\ <<<A> -> <C>> /\ <<C> -> <D>>>>> -> <D>
s2prf3 = ruleFantasy (\premise -> let prfA = fromRight $ ruleSepL premise in let prfAtoCCtoD = fromRight $ ruleSepR $ fromRight $ ruleSepR premise in let prfAtoC = fromRight $ ruleSepL prfAtoCCtoD in let prfCtoD = fromRight $ ruleSepR prfAtoCCtoD in fromRight $ ruleDetachment (fromRight $ ruleDetachment prfA prfAtoC) prfCtoD) (And (PropVar (Var A)) (And (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var B)) (PropVar (Var D)))) (And (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var C)) (PropVar (Var D))))))
-- |- <A> -> <<<A> -> <A>> -> <A>>
s2prf4 = ruleFantasy (\prfA -> ruleFantasy (\prfAimpA -> fromRight $ ruleDetachment prfA prfAimpA) (Imp (PropVar (Var A)) (PropVar (Var A)))) (PropVar (Var A))
-- |- <<<A> -> <B>> /\ <<B> -> <C>>> -> <<A> -> <C>>
s2prf5 = ruleFantasy (\premise -> let prfAtoB = fromRight $ ruleSepL premise in let prfBtoC = fromRight $ ruleSepR premise in ruleFantasy (\prfA -> let prfB = fromRight $ ruleDetachment prfA prfAtoB in fromRight $ ruleDetachment prfB prfBtoC) (PropVar (Var A))) (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var B)) (PropVar (Var C))))
-- |- <<<A> -> <B>> /\ <<A> -> <<B> -> <C>>>> -> <<A> -> <C>>
s2prf6 = ruleFantasy (\premise -> let prfAtoB = fromRight $ ruleSepL premise in let prfAtoBtoC = fromRight $ ruleSepR premise in ruleFantasy (\prfA -> let prfB = fromRight $ ruleDetachment prfA prfAtoB in fromRight $ ruleDetachment prfB $ fromRight $ ruleDetachment prfA prfAtoBtoC) (PropVar (Var A))) (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var A)) (Imp (PropVar (Var B)) (PropVar (Var C)))))
-- |- <A> -> <A>
s2prf7 = ruleFantasy id (PropVar (Var A))
-- |- <<<<A> -> <C>> /\ <<B> -> <C>>> /\ <<A> /\ <B>>> -> <C>
s2prf8 = ruleFantasy (\premise -> let prfAtoCBtoC = fromRight $ ruleSepL premise in let prfAtoC = fromRight $ ruleSepL prfAtoCBtoC in let prfAB = fromRight $ ruleSepR premise in let prfA = fromRight $ ruleSepL prfAB in fromRight $ ruleDetachment prfA prfAtoC) (And (And (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var B)) (PropVar (Var C)))) (And (PropVar (Var A)) (PropVar (Var B))))
-- |- <<<A> -> <C>> /\ <<B> -> <C>>> -> <<<A> /\ <B>> -> <C>>
s2prf9 = ruleFantasy (\premise -> let prfAtoC = fromRight $ ruleSepL premise in ruleFantasy (\prfAB -> let prfA = fromRight $ ruleSepL prfAB in fromRight $ ruleDetachment prfA prfAtoC) (And (PropVar (Var A)) (PropVar (Var B)))) (And (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var B)) (PropVar (Var C))))
-- |- <B> -> <<A> -> <B>>
s2prf10 = ruleFantasy (\prfB -> ruleFantasy (\prfA -> prfB) (PropVar (Var A))) (PropVar (Var B))
-- |- <<<A> /\ <B>> -> <C>> -> <<A> -> <<B> -> <C>>>
s2prf11 = ruleFantasy (\prfABtoC -> ruleFantasy (\prfA -> ruleFantasy (\prfB -> fromRight $ ruleDetachment (ruleJoin prfA prfB) prfABtoC) (PropVar (Var B))) (PropVar (Var A))) (Imp (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<A> -> <<B> -> <C>>> -> <<<A> /\ <B>> -> <C>>
s2prf12 = ruleFantasy (\prfAtoBtoC -> ruleFantasy (\prfAB -> let prfA = fromRight $ ruleSepL prfAB in let prfB = fromRight $ ruleSepR prfAB in let prfBtoC = fromRight $ ruleDetachment prfA prfAtoBtoC in fromRight $ ruleDetachment prfB prfBtoC) (And (PropVar (Var A)) (PropVar (Var B)))) (Imp (PropVar (Var A)) (Imp (PropVar (Var B)) (PropVar (Var C))))
-- |- <<<A> -> <B>> /\ <<A> -> <C>>> -> <<A> -> <<B> /\ <C>>>
s2prf13 = ruleFantasy (\prfAtoBAtoC -> ruleFantasy (\prfA -> let prfAtoB = fromRight $ ruleSepL prfAtoBAtoC in let prfAtoC = fromRight $ ruleSepR prfAtoBAtoC in let prfB = fromRight $ ruleDetachment prfA prfAtoB in let prfC = fromRight $ ruleDetachment prfA prfAtoC in ruleJoin prfB prfC) (PropVar (Var A))) (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var A)) (PropVar (Var C))))
-- |- <<<A> -> <<A> -> <B>>> /\ <<<A> -> <B>> -> <B>>> -> <B>
s2prf14 = ruleFantasy f (And (Imp (PropVar (Var A)) (Imp (PropVar (Var A)) (PropVar (Var B)))) (Imp (Imp (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var B))))
  where
  f premise =
   let prfAtoAtoB = fromRight $ ruleSepL premise
       prfAtoBtoA = fromRight $ ruleSepR premise
       disjElim = s3lemma3 (Imp (PropVar (Var A)) (PropVar (Var B))) (Not (Imp (PropVar (Var A)) (PropVar (Var B)))) (PropVar (Var B))
       excld    = fromRight $ exclMiddle (Imp (PropVar (Var A)) (PropVar (Var B)))
       p1       = ruleFantasy (\prfAtoB -> fromRight $ ruleDetachment prfAtoB prfAtoBtoA) (Imp (PropVar (Var A)) (PropVar (Var B)))
       p2       = ruleFantasy (\prfnotAtoB -> let prfAnotB = s1lemma1 (PropVar (Var A)) (PropVar (Var B)) in let prfA = fromRight $ ruleSepL $ fromRight $ ruleDetachment prfnotAtoB prfAnotB in fromRight $ ruleDetachment prfA (fromRight $ ruleDetachment prfA prfAtoAtoB)) (Not (Imp (PropVar (Var A)) (PropVar (Var B))))
       in fromRight $ ruleDetachment excld $ fromRight $ ruleDetachment (ruleJoin p1 p2) disjElim

-- | Session 3
-- |- <x> -> <<x> \/ <y>>
s3lemma1 x y =
  let f premise =
       let f premise' = fromRight $ ruleDetachment (ruleJoin premise premise') (s4lemma1 x y)
           step1 = ruleFantasy f (Not x)
           step2 = fromRight $ ruleSwitcheroo step1
           in step2
  in ruleFantasy f x
-- |- <<x> \/ <y>> -> <<y> \/ <x>>
s3lemma2 x y = ruleFantasy (\x -> applyPropRule [GoRight] (fromRight . ruleDoubleTildeElim) (fromRight $ ruleSwitcheroo $ fromRight $ ruleContra $ fromRight $ ruleSwitcheroo x)) (Or x y)
-- |- <<<a> \/ <b>> /\ <<<a> -> <c>> /\ <<b> -> <c>>>> -> <c> (props int-e@freenode)
s3lemma3 a b c = ruleFantasy
  f
  (And (Imp a c) (Imp b c))
    where
    f premise =
      ruleFantasy f' (Or a b)
      where
      f' prfAorB =
        let prfAimpC = fromRight $ ruleSepL premise
            prfBimpC = fromRight $ ruleSepR premise
            prfCornotC = fromRight $ exclMiddle c
            prfnotAtoB = fromRight $ ruleSwitcheroo prfAorB
            prfnotCtoBottom = ruleFantasy f (Not c)
              where
              f premise' = let prfnotA = fromRight $ ruleDetachment premise' $ fromRight $ ruleContra prfAimpC
                               prfB = fromRight $ ruleDetachment prfnotA $ fromRight $ ruleSwitcheroo prfAorB
                               prfC = fromRight $ ruleDetachment prfB prfBimpC
                           in ruleJoin premise' prfC
            prfnotCtoBottom'  = applyPropRule [GoRight,GoRight] ruleDoubleTildeIntro prfnotCtoBottom
            prfnotCtoBottom'' = applyPropRule [GoRight] (fromRight . ruleDeMorgan) prfnotCtoBottom'
            prfCornotCtoC     = fromRight $ ruleContra prfnotCtoBottom''
        in fromRight $ ruleDetachment prfCornotC prfCornotCtoC

-- |- <<A> /\ <B>> -> <<A> \/ <B>>
s3prf1 = ruleFantasy (\prfAB -> let prfA = fromRight $ ruleSepL prfAB in fromRight $ ruleDetachment prfA (s3lemma1 (PropVar (Var A)) (PropVar (Var B)))) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <A> -> <<A> \/ <B>>
s3prf2 = s3lemma1 (PropVar $ Var A) (PropVar $ Var B)
-- |- <B> -> <<A> \/ <B>>
s3prf3 = applyPropRule [GoRight] (\prf -> fromRight $ ruleDetachment prf $ s3lemma2 (PropVar $ Var B) (PropVar $ Var A)) (s3lemma1 (PropVar $ Var B) (PropVar $ Var A))
-- |- <A> -> <<A> \/ <A>>
s3prf4 = s3lemma1 (PropVar $ Var A) (PropVar $ Var A)
-- |- <<A> \/ <B>> -> <<B> \/ <A>>
s3prf5 = s3lemma2 (PropVar $ Var A) (PropVar $ Var B)
-- |- <<A> \/ <<B> \/ <C>>> -> <<<A> \/ <B>> \/ <C>>
s3prf6 =
  let f prfAorBorC =
       let prf = s3lemma3 (PropVar $ Var A) (Or (PropVar $ Var B) (PropVar $ Var C)) (Or (Or (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
           prf1 =
            let f' prfA =
                 let prfAorB = fromRight $ ruleDetachment prfA $ s3lemma1 (PropVar $ Var A) (PropVar $ Var B)
                     prfAorBorC = fromRight $ ruleDetachment prfAorB $ s3lemma1 (Or (PropVar $ Var A) (PropVar $ Var B)) (PropVar $ Var C)
                     in prfAorBorC
                in ruleFantasy f' (PropVar $ Var A)
           prf2 =
            let f' prfBorC =
                 let prf' = s3lemma3 (PropVar $ Var B) (PropVar $ Var C) (Or (Or (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
                     prf1 =
                      let f' prfB =
                           let prfBorA = fromRight $ ruleDetachment prfB $ s3lemma1 (PropVar $ Var B) (PropVar $ Var A)
                               prfAorB = fromRight $ ruleDetachment prfBorA $ s3lemma2 (PropVar $ Var B) (PropVar $ Var A)
                               prfAorBorC = fromRight $ ruleDetachment prfAorB $ s3lemma1 (Or (PropVar $ Var A) (PropVar $ Var B)) (PropVar $ Var C)
                               in prfAorBorC
                           in ruleFantasy f' (PropVar $ Var B)
                     prf2 =
                      let f' prfC =
                           let prfCorAorB = fromRight $ ruleDetachment prfC $ s3lemma1 (PropVar $ Var C) (Or (PropVar $ Var A) (PropVar $ Var B))
                               prfAorBorC = fromRight $ ruleDetachment prfCorAorB $ s3lemma2 (PropVar $ Var C) (Or (PropVar $ Var A) (PropVar $ Var B))
                               in prfAorBorC
                           in ruleFantasy f' (PropVar $ Var C)
                     joined = ruleJoin prf1 prf2
                     in fromRight $ ruleDetachment prfBorC $ fromRight $ ruleDetachment joined prf'
                in ruleFantasy f' (Or (PropVar $ Var B) (PropVar $ Var C))
           joined = ruleJoin prf1 prf2
       in fromRight $ ruleDetachment prfAorBorC $ fromRight $ ruleDetachment joined prf
  in ruleFantasy f (Or (PropVar (Var A)) (Or (PropVar (Var B)) (PropVar (Var C))))
-- |- <<A> /\ <B>> -> <<A> \/ <B>>
s3prf7 = s3prf1
-- |- <<<A> /\ <B>> \/ <C>> -> <<<A> \/ <C>> /\ <<B> \/ <C>>>
s3prf8 =
  let f prfAandBorC =
       let prf = s3lemma3 (And (PropVar $ Var A) (PropVar $ Var B)) (PropVar $ Var C) (And (Or (PropVar (Var A)) (PropVar (Var C))) (Or (PropVar (Var B)) (PropVar (Var C))))
           prf1 =
            let f' prfAandB =
                 let prfA = fromRight $ ruleSepL prfAandB
                     prfB = fromRight $ ruleSepR prfAandB
                     prfAorC = fromRight $ ruleDetachment prfA $ s3lemma1 (PropVar $ Var A) (PropVar $ Var C)
                     prfBorC = fromRight $ ruleDetachment prfB $ s3lemma1 (PropVar $ Var B) (PropVar $ Var C)
                     in ruleJoin prfAorC prfBorC
                in ruleFantasy f' (And (PropVar $ Var A) (PropVar $ Var B))
           prf2 =
            let f' prfC =
                 let prfCorA = fromRight $ ruleDetachment prfC $ s3lemma1 (PropVar $ Var C) (PropVar $ Var A)
                     prfCorB = fromRight $ ruleDetachment prfC $ s3lemma1 (PropVar $ Var C) (PropVar $ Var B)
                     prfAorC = fromRight $ ruleDetachment prfCorA $ s3lemma2 (PropVar $ Var C) (PropVar $ Var A)
                     prfBorC = fromRight $ ruleDetachment prfCorB $ s3lemma2 (PropVar $ Var C) (PropVar $ Var B)
                     in ruleJoin prfAorC prfBorC
                in ruleFantasy f' (PropVar $ Var C)
           joined = ruleJoin prf1 prf2
       in fromRight $ ruleDetachment prfAandBorC $ fromRight $ ruleDetachment joined prf
  in ruleFantasy f (Or (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> \/ <B>> /\ <C>> -> <<<A> /\ <C>> \/ <<B> /\ <C>>>
s3prf9 =
  let f prfAorBandC =
       let prfAorB = fromRight $ ruleSepL prfAorBandC
           prfC    = fromRight $ ruleSepR prfAorBandC
           prf     = s3lemma3 (PropVar $ Var A) (PropVar $ Var B) (Or (And (PropVar (Var A)) (PropVar (Var C))) (And (PropVar (Var B)) (PropVar (Var C))))
           prf1    =
            let f' prfA =
                 let prfAandC = ruleJoin prfA prfC
                     prfAandCorBandC = fromRight $ ruleDetachment prfAandC $ s3lemma1 (And (PropVar $ Var A) (PropVar $ Var C)) (And (PropVar $ Var B) (PropVar $ Var C))
                     in prfAandCorBandC
                in ruleFantasy f' (PropVar $ Var A)
           prf2    =
            let f' prfB =
                 let prfBandC = ruleJoin prfB prfC
                     prfBandCorAandC = fromRight $ ruleDetachment prfBandC $ s3lemma1 (And (PropVar $ Var B) (PropVar $ Var C)) (And (PropVar $ Var A) (PropVar $ Var C))
                     prfAandCorBandC = fromRight $ ruleDetachment prfBandCorAandC $ s3lemma2 (And (PropVar $ Var B) (PropVar $ Var C)) (And (PropVar $ Var A) (PropVar $ Var C))
                     in prfAandCorBandC
                in ruleFantasy f' (PropVar $ Var B)
           joined = ruleJoin prf1 prf2
           in fromRight $ ruleDetachment prfAorB $ fromRight $ ruleDetachment joined prf
  in ruleFantasy f (And (Or (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> \/ <B>> /\ <<<A> -> <C>> /\ <<B> -> <C>>>> -> <C>
s3prf10 = s3lemma3 (PropVar $ Var A) (PropVar $ Var B) (PropVar $ Var C)
-- |- <<<A> \/ <B>> -> <C>> -> <<<A> -> <C>> /\ <<B> -> <C>>>
s3prf11 =
  let f prfAorBimpC =
       let step1 = applyPropRule [GoLeft] ruleDoubleTildeIntro prfAorBimpC
           step2 = applyPropRule [GoLeft,GoLeft] (fromRight . ruleDeMorgan) step1
           prfnotAandnotBorC = fromRight $ ruleSwitcheroo step2
           prf = s3lemma3 (And (Not (PropVar $ Var A)) (Not (PropVar $ Var B))) (PropVar $ Var C) (And (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var B)) (PropVar (Var C))))
           prf1 =
            let f' prfnotAandnotB =
                 let prfnotA = fromRight $ ruleSepL prfnotAandnotB
                     prfnotB = fromRight $ ruleSepR prfnotAandnotB
                     prfnotCimpnotA = ruleFantasy (\_ -> prfnotA) (Not (PropVar (Var C)))
                     prfnotBimpnotA = ruleFantasy (\_ -> prfnotB) (Not (PropVar (Var C)))
                     prfAimpC = fromRight $ ruleContra prfnotCimpnotA
                     prfBimpC = fromRight $ ruleContra prfnotBimpnotA
                     in ruleJoin prfAimpC prfBimpC
                in ruleFantasy f' (And (Not (PropVar $ Var A)) (Not (PropVar $ Var B)))
           prf2 =
            let f' prfC =
                 let prfCAimpC = ruleFantasy (\_ -> prfC) (PropVar (Var A))
                     prfCBimpC = ruleFantasy (\_ -> prfC) (PropVar (Var B))
                     in ruleJoin prfCAimpC prfCBimpC
                in ruleFantasy f' (PropVar $ Var C)
           joined = ruleJoin prf1 prf2
       in fromRight $ ruleDetachment prfnotAandnotBorC $ fromRight $ ruleDetachment joined prf
  in ruleFantasy f (Imp (Or (PropVar $ Var A) (PropVar $ Var B)) (PropVar $ Var C))
-- |- <<<A> -> <B>> \/ <<A> -> <C>>> -> <<A> -> <<B> \/ <C>>>
s3prf12 =
  let f prfAimpBorAimpC =
       let f' prfA =
            let prf = s3lemma3 (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var A)) (PropVar (Var C))) (Imp (PropVar (Var A)) (Or (PropVar (Var B)) (PropVar (Var C))))
                prf1 =
                 let f' prfAimpB =
                      let prfB = fromRight $ ruleDetachment prfA prfAimpB
                          prfBorC = fromRight $ ruleDetachment prfB $ s3lemma1 (PropVar (Var B)) (PropVar (Var C))
                          in ruleFantasy (\_ -> prfBorC) (PropVar (Var A))
                     in ruleFantasy f' (Imp (PropVar (Var A)) (PropVar (Var B)))
                prf2 =
                 let f' prfAimpC =
                      let prfC = fromRight $ ruleDetachment prfA prfAimpC
                          prfCorB = fromRight $ ruleDetachment prfC $ s3lemma1 (PropVar (Var C)) (PropVar (Var B))
                          prfBorC = fromRight $ ruleDetachment prfCorB $ s3lemma2 (PropVar $ Var C) (PropVar $ Var B)
                          in ruleFantasy (\_ -> prfBorC) (PropVar (Var A))
                     in ruleFantasy f' (Imp (PropVar (Var A)) (PropVar (Var C)))
                joined = ruleJoin prf1 prf2
            in fromRight $ ruleDetachment prfA $ fromRight $ ruleDetachment prfAimpBorAimpC $ fromRight $ ruleDetachment joined prf
           in ruleFantasy f' (PropVar (Var A))
  in ruleFantasy f (Or (Imp (PropVar $ Var A) (PropVar $ Var B)) (Imp (PropVar $ Var A) (PropVar $ Var C)))

-- | Session 4
-- |- <<x> /\ <~x>> -> <y>
s4lemma1 x y =
  let f premise =
       let left = fromRight $ ruleSepL premise
           right = fromRight $ ruleSepR premise
           prfImp =
             let f _ = ruleDoubleTildeIntro left
                 step1 = ruleFantasy f (Not y)
                 step2 = fromRight $ ruleContra step1
             in step2
       in fromRight $ ruleDetachment right prfImp
  in ruleFantasy f (bottom x)

-- |- <<A> /\ <~A>> -> <A>
s4prf1 = s4lemma1 (PropVar $ Var A) (PropVar $ Var A)

-- | Hilbert system
-- |- <<a> \/ <a>> -> <a>
hlemma1 a =
  let f prfAorA =
       let prf = s3lemma3 a a a
           prfAtoA = ruleFantasy id (PropVar (Var A))
           joined = ruleJoin prfAtoA prfAtoA
       in fromRight $ ruleDetachment prfAorA $ fromRight $ ruleDetachment joined prf
  in ruleFantasy f (Or a a)

-- |- <A> -> <A>
hprf1 = ruleFantasy id (PropVar (Var A))
-- |- <<B> -> <C>> -> <<<A> -> <B>> -> <<A> -> <C>>>
hprf2 = ruleFantasy (\prfBtoC -> ruleFantasy (\prfAtoB -> ruleFantasy (\prfA -> let prfB = fromRight $ ruleDetachment prfA prfAtoB in fromRight $ ruleDetachment prfB prfBtoC) (PropVar (Var A))) (Imp (PropVar (Var A)) (PropVar (Var B)))) (Imp (PropVar (Var B)) (PropVar (Var C)))
-- |- <<A> -> <<B> -> <C>>> -> <<B> -> <<A> -> <C>>>
hprf3 = ruleFantasy (\prfAtoBtoC -> ruleFantasy (\prfB -> ruleFantasy (\prfA -> let prfBtoC = fromRight $ ruleDetachment prfA prfAtoBtoC in fromRight $ ruleDetachment prfB prfBtoC) (PropVar (Var A))) (PropVar (Var B))) (Imp (PropVar (Var A)) (Imp (PropVar (Var B)) (PropVar (Var C))))
-- |- <~A> -> <<A> -> <B>>
hprf4 = ruleFantasy (\prfnotA -> ruleFantasy (\prfA -> fromRight $ ruleDetachment (ruleJoin prfA prfnotA) $ s4lemma1 (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var A))) (Not (PropVar (Var A)))
-- |- <<~A> -> <A>> -> <A>
hprf5 =
  let f prfnotAtoB =
       let prfAorA = fromRight $ ruleSwitcheroo prfnotAtoB
       in fromRight $ ruleDetachment prfAorA (hlemma1 (PropVar (Var A)))
  in ruleFantasy f (Imp (Not (PropVar (Var A))) (PropVar (Var A)))
-- |- <~~A> -> <A>
hprf6 = ruleFantasy (fromRight . ruleDoubleTildeElim) (Not (Not (PropVar (Var A))))
-- |- <A> -> <~~A>
hprf7 = ruleFantasy ruleDoubleTildeIntro (PropVar (Var A))
-- |- <<B> -> <A>> -> <<~A> -> <~B>>
hprf8 = ruleFantasy (fromRight . ruleContra) (Imp (PropVar (Var B)) (PropVar (Var A)))
-- |- <<A> -> <B>> -> <<<~A> -> <B>> -> <B>>
hprf9 =
  let f prfAtoB =
       let f' prfnotAtoB =
            let prf = s3lemma3 (PropVar $ Var A) (Not (PropVar $ Var A)) (PropVar (Var B))
                prfAornotA = fromRight $ exclMiddle (PropVar (Var A))
                joined = ruleJoin prfAtoB prfnotAtoB
            in fromRight $ ruleDetachment prfAornotA $ fromRight $ ruleDetachment joined prf
       in ruleFantasy f' (Imp (Not (PropVar (Var A))) (PropVar (Var B)))
  in ruleFantasy f (Imp (PropVar (Var A)) (PropVar (Var B)))
