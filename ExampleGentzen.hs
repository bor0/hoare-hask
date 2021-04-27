module ExampleGentzen where

import TNT
import Gentzen
import Common

-- Helpers
bottom x = And x (Not x)
-- |- <A> \/ <~A>
exclMiddle x = ruleSwitcheroo $ ruleFantasy id (Not x)

-- Example proofs for exercises taken from http://incredible.pm/

-- | Session 1
-- |- <A> -> <A>
s1prf1 = ruleFantasy id (PropVar (Var A))
-- |- <A> -> <<B> -> <A>>
s1prf2 = ruleFantasy (\prfA -> ruleFantasy (\prfB -> prfA) (PropVar (Var B))) (PropVar (Var A))
-- |- <A> -> <<B> -> <B>>
s1prf3 = ruleFantasy (\prfA -> ruleFantasy (\prfB -> prfB) (PropVar (Var B))) (PropVar (Var A))
-- |- <A> -> <<B> -> <<A> /\ <B>>>
s1prf4 = ruleFantasy (\prfA -> ruleFantasy (\prfB -> ruleJoin prfA prfB) (PropVar (Var B))) (PropVar (Var A))
-- |- <A> -> <<A> /\ <A>>
s1prf5 = ruleFantasy (\prfA -> ruleJoin prfA prfA) (PropVar (Var A))
-- |- <<A> /\ <B>> -> <A>
s1prf6 = ruleFantasy (\prfAB -> ruleSepL prfAB) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <B>
s1prf7 = ruleFantasy (\prfAB -> ruleSepR prfAB) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <<A> /\ <B>>
s1prf8 = ruleFantasy id (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> /\ <B>> -> <<B> /\ <A>>
s1prf9 = ruleFantasy (\prfAB -> ruleJoin (ruleSepR prfAB) (ruleSepL prfAB)) (And (PropVar (Var A)) (PropVar (Var B)))
-- |- <<<A> /\ <B>> /\ <C>> -> <A>
s1prf10 = ruleFantasy (\prfABC -> ruleSepL $ ruleSepL prfABC) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> /\ <B>> /\ <C>> -> <B>
s1prf11 = ruleFantasy (\prfABC -> ruleSepR $ ruleSepL prfABC) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> /\ <B>> /\ <C>> -> <C>
s1prf12 = ruleFantasy (\prfABC -> ruleSepR prfABC) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> /\ <B>> /\ <C>> -> <<A> /\ <C>>
s1prf13 = ruleFantasy (\prfABC -> ruleJoin (ruleSepL $ ruleSepL prfABC) (ruleSepR prfABC)) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<<A> /\ <B>> /\ <C>> -> <<A> /\ <<B> /\ <C>>>
s1prf14 = ruleFantasy (\prfABC -> ruleJoin (ruleSepL $ ruleSepL prfABC) (ruleJoin (ruleSepR $ ruleSepL prfABC) (ruleSepR prfABC))) (And (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))

-- | Session 2
-- |- <A> -> <<<A> -> <B>> -> <B>>
s2prf1 = ruleFantasy (\prfA -> ruleFantasy (\prfAimpB -> rightProof $ ruleDetachment prfA prfAimpB) (Imp (PropVar (Var A)) (PropVar (Var B)))) (PropVar (Var A))
-- |- <A> -> <<<A> -> <B>> -> <<<B> -> <C>> -> <C>>>
s2prf2 = ruleFantasy (\prfA -> ruleFantasy (\prfAimpB -> ruleFantasy (\prfBimpC -> rightProof $ ruleDetachment (rightProof $ ruleDetachment prfA prfAimpB) prfBimpC) (Imp (PropVar (Var B)) (PropVar (Var C)))) (Imp (PropVar (Var A)) (PropVar (Var B)))) (PropVar (Var A))
-- |- <A> -> <<<A> -> <A>> -> <A>>
s2prf3 = ruleFantasy (\prfA -> ruleFantasy (\prfAimpA -> rightProof $ ruleDetachment prfA prfAimpA) (Imp (PropVar (Var A)) (PropVar (Var A)))) (PropVar (Var A))
-- |- <<A> -> <B>> -> <<<A> -> <<B> -> <C>>> -> <<A> -> <C>>>
s2prf4 = ruleFantasy (\prfAimpB -> ruleFantasy (\prfAimpBimpC -> ruleFantasy (\prfA -> let prfB = rightProof $ ruleDetachment prfA prfAimpB in rightProof $ ruleDetachment prfB $ rightProof $ ruleDetachment prfA prfAimpBimpC) (PropVar (Var A))) (Imp (PropVar (Var A)) (Imp (PropVar (Var B)) (PropVar (Var C))))) (Imp (PropVar (Var A)) (PropVar (Var B)))
-- |- <<A> -> <C>> -> <<<B> -> <C>> -> <<<A> /\ <B>> -> <C>>>
s2prf5 = ruleFantasy (\prfAimpC -> ruleFantasy (\prfBimpC -> ruleFantasy (\prfAB -> let prfA = ruleSepL prfAB in rightProof $ ruleDetachment prfA prfAimpC) (And (PropVar (Var A)) (PropVar (Var B)))) (Imp (PropVar (Var B)) (PropVar (Var C)))) (Imp (PropVar (Var A)) (PropVar (Var C)))
-- |- <B> -> <<A> -> <B>>
s2prf6 = ruleFantasy (\prfB -> ruleFantasy (\prfA -> prfB) (PropVar (Var A))) (PropVar (Var B))
-- |- <<<A> /\ <B>> -> <C>> -> <<A> -> <<B> -> <C>>>
s2prf7 = ruleFantasy (\prfABimpC -> ruleFantasy (\prfA -> ruleFantasy (\prfB -> rightProof $ ruleDetachment (ruleJoin prfA prfB) prfABimpC) (PropVar (Var B))) (PropVar (Var A))) (Imp (And (PropVar (Var A)) (PropVar (Var B))) (PropVar (Var C)))
-- |- <<A> -> <<B> -> <C>>> -> <<<A> /\ <B>> -> <C>>
s2prf8 = ruleFantasy (\prfAimpBimpC -> ruleFantasy (\prfAB -> let prfA = ruleSepL prfAB in let prfB = ruleSepR prfAB in let prfBimpC = rightProof $ ruleDetachment prfA prfAimpBimpC in rightProof $ ruleDetachment prfB prfBimpC) (And (PropVar (Var A)) (PropVar (Var B)))) (Imp (PropVar (Var A)) (Imp (PropVar (Var B)) (PropVar (Var C))))
-- |- <<<A> -> <B>> /\ <<A> -> <C>>> -> <<A> -> <<B> /\ <C>>>
s2prf9 = ruleFantasy (\prfAimpBAimpC -> ruleFantasy (\prfA -> let prfAimpB = ruleSepL prfAimpBAimpC in let prfAimpC = ruleSepR prfAimpBAimpC in let prfB = rightProof $ ruleDetachment prfA prfAimpB in let prfC = rightProof $ ruleDetachment prfA prfAimpC in ruleJoin prfB prfC) (PropVar (Var A))) (And (Imp (PropVar (Var A)) (PropVar (Var B))) (Imp (PropVar (Var A)) (PropVar (Var C))))

-- | Session 3
-- |- <x> -> <<x> \/ <y>>
s3lemma1 x y =
  let f premise =
       let f premise' = rightProof $ ruleDetachment (ruleJoin premise premise') (s4lemma1 x y)
           step1 = ruleFantasy f (Not x)
           step2 = ruleSwitcheroo step1
           in step2
  in ruleFantasy f x

s3lemma2 x y = ruleFantasy (\x -> applyPropRule [GoRight] ruleDoubleTildeElim $ ruleSwitcheroo $ ruleContra $ ruleSwitcheroo x) (Or x y)

-- |- <A> -> <<A> \/ <B>>
s3prf1 = s3lemma1 (PropVar $ Var A) (PropVar $ Var B)
-- |- <B> -> <<A> \/ <B>>
s3prf2 = applyPropRule [GoRight] (\prf -> rightProof $ ruleDetachment prf s3prf4') (s3lemma1 (PropVar $ Var B) (PropVar $ Var A))
-- |- <A> -> <<A> \/ <A>>
s3prf3 = s3lemma1 (PropVar $ Var A) (PropVar $ Var A)
-- |- <<A> \/ <B>> -> <<B> \/ <A>>
s3prf4 = s3lemma2 (PropVar $ Var A) (PropVar $ Var B)
-- |- <<B> \/ <A>> -> <<A> \/ <B>>
s3prf4' = s3lemma2 (PropVar $ Var B) (PropVar $ Var A)
-- |- <<A> \/ <<B> /\ <C>>> -> <<<B> /\ <C>> \/ <A>>
s3prf5 = s3lemma2 (PropVar $ Var A) (And (PropVar (Var B)) (PropVar (Var C)))
-- |- <<A> /\ <B>> -> <<A> \/ <B>>
s3prf6 x y = ruleFantasy (\prfAB -> let prfA = ruleSepL prfAB in rightProof $ ruleDetachment prfA (s3lemma1 x y)) (And x y)
s3prf6' = s3prf6 (PropVar $ Var A) (PropVar $ Var B)

s3prf7 = ruleFantasy id (Or (And (PropVar $ Var A) (PropVar $ Var B)) (PropVar $ Var C))

-- |- <<<A> \/ <B>> /\ <~A>> -> <B>
s3prf8 x y = ruleFantasy (\prf -> let prfAorB = ruleSepL prf in let prfNotA = ruleSepR prf in rightProof $ ruleDetachment prfNotA (ruleSwitcheroo prfAorB)) (And (Or x y) (Not x))
s3prf8' = s3prf8 (PropVar $ Var A) (PropVar $ Var B)

-- |- <<<A> \/ <B>> /\ <<<A> -> <C>> /\ <<B> -> <C>>>> -> <C> (props int-e@freenode)
s3prf9 = ruleFantasy
  f
  (And (Or (PropVar $ Var A) (PropVar $ Var B)) (And (Imp (PropVar $ Var A) (PropVar $ Var C)) (Imp (PropVar $ Var B) (PropVar $ Var C))))
    where
    f premise =
      let prfAorB  = ruleSepL premise
          prfAimpC = ruleSepL $ ruleSepR premise
          prfBimpC = ruleSepR $ ruleSepR premise
          prfCornotC = exclMiddle (PropVar $ Var C)
          prfnotAtoB = ruleSwitcheroo prfAorB
          prfnotCtoBottom = ruleFantasy f (Not (PropVar $ Var C))
            where
            f premise' = let prfnotA = rightProof $ ruleDetachment premise' $ ruleContra prfAimpC
                             prfB = rightProof $ ruleDetachment prfnotA $ ruleSwitcheroo prfAorB
                             prfC = rightProof $ ruleDetachment prfB prfBimpC
                         in ruleJoin premise' prfC
          prfnotCtoBottom'  = applyPropRule [GoRight,GoRight] ruleDoubleTildeIntro prfnotCtoBottom
          prfnotCtoBottom'' = applyPropRule [GoRight] ruleDeMorgan prfnotCtoBottom'
          prfBottomtoC      = ruleContra prfnotCtoBottom''
      in rightProof $ ruleDetachment prfCornotC prfBottomtoC

-- | Session 4
-- |- <<x> /\ <~x>> -> <y>
s4lemma1 x y =
  let f premise =
       let left = ruleSepL premise
           right = ruleSepR premise
           prfImp =
             let f _ = ruleDoubleTildeIntro left
                 step1 = ruleFantasy f (Not y)
                 step2 = ruleContra step1
             in step2
       in rightProof $ ruleDetachment right prfImp
  in ruleFantasy f (bottom x)

-- |- <<A> /\ <~A>> -> <A>
s4prf1 = s4lemma1 (PropVar $ Var A) (PropVar $ Var A)
