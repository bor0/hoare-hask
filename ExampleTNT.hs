module ExampleTNT where

import TNT
import Gentzen
import Common

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
           in ruleGeneralize step11 D (Just premise)
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

-- |- All C:All D:((D)+(S(C)))=((S(D))+(C))
theorem = rightProof $ ruleInduction lemma2 lemma1
