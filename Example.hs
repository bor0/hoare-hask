import Imp
import TNT
import Gentzen
import Hoare
import Common

import qualified Data.Map as M

data Vars = A | B | C | D deriving (Eq, Ord, Show)

-- Program definition
countToB =
  let l1 = CAssign A Z
      l2 = CWhile (Not (PropVar $ Eq (Var A) (Var B))) l3
      l3 = CAssign A (S (Var A))
  in CSequence l1 l2

-- Example evaluation
egEval = eval (M.fromList [(B, 3)]) countToB

-- |- All C:<All D:((D)+(S(C)))=((S(D))+(C))> -> <All D:((D)+(S(S(C))))=((S(D))+(S(C)))>
lemma1 =
  -- |- All A:All B:((A)+(S(B)))=(S((A)+(B)))
  let step1 = axiom3 A B
      -- |- All B:((D)+(S(B)))=(S((D)+(B)))
      step2 = ruleSpec step1 A (Var D)
      -- |- ((D)+(S(S(C))))=(S((D)+(S(C))))
      step3 = ruleSpec step2 B (S (Var C))
      -- |- All B:((S(D))+(S(B)))=(S((S(D))+(B)))
      step4 = ruleSpec step1 A (S (Var D))
      -- |- ((S(D))+(S(C)))=(S((S(D))+(C)))
      step5 = ruleSpec step4 B (Var C)
      -- |- (S((S(D))+(C)))=((S(D))+(S(C)))
      step6 = ruleSymmetry step5
      -- All D:((D)+(S(C)))=((S(D))+(C))
      premise = PropVar (ForAll D (PropVar (Eq (Plus (Var D) (S (Var C))) (Plus (S (Var D)) (Var C)))))
      f premise =
       -- |- ((D)+(S(C)))=((S(D))+(C))
       let step8 = ruleSpec premise D (Var D)
           -- |- (S((D)+(S(C))))=(S((S(D))+(C)))
           step9 = ruleAddS step8
           -- |- ((D)+(S(S(C))))=(S((S(D))+(C)))
           step10 = ruleTransitivity step3 step9
           -- |- ((D)+(S(S(C))))=((S(D))+(S(C)))
           step11 = ruleTransitivity step10 step6
           -- |- All D:((D)+(S(S(C))))=((S(D))+(S(C)))
           step12 = ruleGeneralize step11 D (Just premise)
       in step12
      -- |- <All D:((D)+(S(C)))=((S(D))+(C))> -> <All D:((D)+(S(S(C))))=((S(D))+(S(C)))>
      step7 = ruleFantasy f premise in
      -- |- All C:<All D:((D)+(S(C)))=((S(D))+(C))> -> <All D:((D)+(S(S(C))))=((S(D))+(S(C)))>
      ruleGeneralize step7 C Nothing

-- |- All D:((D)+(S(0)))=((S(D))+(0))
lemma2 =
  -- |- All A:All B:((A)+(S(B)))=(S((A)+(B)))
  let step1 = axiom3 A B
      -- |- All B:((D)+(S(B)))=(S((D)+(B)))
      step2 = ruleSpec step1 A (Var D)
      -- |- ((D)+(S(S(C))))=(S((D)+(S(C))))
      step3 = ruleSpec step2 B (S (Var C))
      -- |- ((D)+(S(0)))=(S((D)+(0)))
      step4 = ruleSpec step2 B Z
      -- |- All A:((A)+(0))=(A)
      step5 = axiom2 A
      -- |- ((D)+(0))=(D)
      step6 = ruleSpec step5 A (Var D)
      -- |- (S((D)+(0)))=(S(D))
      step7 = ruleAddS step6
      -- |- ((D)+(S(0)))=(S(D))
      step8 = ruleTransitivity step4 step7
      -- |- ((S(D))+(0))=(S(D))
      step9 = ruleSpec step5 A (S (Var D))
      -- |- (S(D))=((S(D))+(0))
      step10 = ruleSymmetry step9
      -- |- ((D)+(S(0)))=((S(D))+(0))
      step11 = ruleTransitivity step8 step10 in
      -- |- All D:((D)+(S(0)))=((S(D))+(0))
      ruleGeneralize step11 D Nothing

theorem = go $ ruleInduction lemma2 lemma1
  where go (Right x) = x

-- |- <<~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>> -> <Exists C:((S(A))+(C))=(B)>
preConseq = 
  let premise = And (Not (PropVar $ Eq (Var A) (Var B))) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))
      f premise =
       -- |- ~~Exists C:((A)+(C))=(B)
       let step1 = ruleDoubleTildeIntro (ruleSepR premise)
           -- |- ~~((A)+(S(C)))=(B)
           step2 = applyFOLRule [GoLeft] (\x -> ruleSpec (ruleInterchangeR x) C (S (Var C))) step1
           -- |- ((A)+(S(C)))=(B)
           step3 = ruleDoubleTildeElim step2
           -- |- ((A)+(S(C)))=((S(A))+(C))
           step4 = ruleSpec (ruleSpec theorem C (Var C)) D (Var A)
           -- |- ((S(A))+(C))=((A)+(S(C)))
           step5 = ruleSymmetry step4
           -- |- ((S(A))+(C))=(B)
           step6 = ruleTransitivity step5 step3
           -- |- Exists C:((S(A))+(C))=(B)
           step7 = ruleExistence step6 C []
       in step7
     -- |- <<~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>> -> <Exists C:((S(A))+(C))=(B)>
     in ruleFantasy f premise

-- |- <Exists C:((A)+(C))=(B)> -> <Exists C:((A)+(C))=(B)>
postConseq = ruleFantasy id (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- {Exists C:((S(A))+(C))=(B)} A := S(A); {Exists C:((A)+(C))=(B)}
step5 = hoareAssignment A (S (Var A)) (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- Right {<~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>} A := S(A); {Exists C:((A)+(C))=(B)}
step4 = hoareConsequence preConseq step5 postConseq

-- {Exists C:((0)+(C))=(B)} A := 0; {Exists C:((A)+(C))=(B)}
step2 = hoareAssignment A Z (PropVar (Exists C (PropVar $ Eq (Plus (Var A) (Var C)) (Var B))))

-- Right {Exists C:((A)+(C))=(B)} (While (~(A)=(B)) Do {A := S(A);}); {<~~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>}
step3 = whenRight step4 hoareWhile

-- Right {Exists C:((0)+(C))=(B)} A := 0; (While (~(A)=(B)) Do {A := S(A);}); {<~~(A)=(B)> /\ <Exists C:((A)+(C))=(B)>}
step1 = whenRight step3 (\step3 -> hoareSequence step2 step3)
