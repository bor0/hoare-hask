module Main where

import Common
import Imp
import Hoare
import TNT
import Gentzen
import qualified Data.Map as M

import Data.List (intercalate)

toArith 0 = Z
toArith x = S (toArith (x - 1))

-- Count X up to 10
countTo10 =
  -- X := 0
  let l1 = CAssign 'X' Z
  -- while ~(X = Y)
      l2 = CWhile (Not (PropVar $ Eq (Var 'X') (toArith 10))) l3
      -- X := X + 1
      l3 = CAssign 'X' (Plus (Var 'X') (S Z))
  in CSequence l1 l2

-- Calculate factorial of X
factX =
  -- Z := 1
  let l1 = CAssign 'Z' (S Z)
  -- Y := 1
      l2 = CAssign 'Y' (S Z)
  -- while ~(Z = X)
      l3 = CWhile (Not (PropVar $ Eq (Var 'Z') (S (Var 'X')))) (CSequence l4 l5)
      -- Y := Y * Z
      l4 = CAssign 'Y' (Mult (Var 'Y') (Var 'Z'))
      -- Z := Z + 1
      l5 = CAssign 'Z' (S (Var 'Z'))
  in CSequence l1 (CSequence l2 l3)

factAssertion f = f
  (PropVar $ Eq (toArith 5) (Var 'X'))
  factX
  (PropVar $ Eq (toArith 120) (Var 'Y'))

-- TODO: Add Gentzen examples

main = do
  -- Arithmetic language example
  let expr = Plus (Var 'X') (toArith 5) in putStrLn $ show expr ++ " = " ++ show (aeval (M.fromList [('X', 5)]) expr)
  -- Boolean language example
  let expr = PropVar (Eq (Var 'X') (toArith 5)) in putStrLn $ show expr ++ " = " ++ show (beval (M.fromList [('X', 5)]) expr)
  -- Eval (run program) example
  putStrLn $ "Calculate the factorial of 5: " ++ show (eval (M.fromList [('X', 5)]) factX)
  -- Assertion example (meta)
  putStrLn $ "(PASS) Assert {X=5} factX {Y=120} (meta): " ++ show (factAssertion (assert (M.fromList [('X', 5)])))
  putStrLn $ "(FAIL) Assert {X=5} factX {Y=120} (meta): " ++ show (factAssertion (assert (M.fromList [('X', 4)])))
  -- Assertion example (object)
  putStrLn $ "(PASS) Assert {X=5} factX {Y=120} (object): " ++ show (eval (M.fromList [('X', 5)]) (factAssertion CAssert))
  putStrLn $ "(FAIL) Assert {X=4} factX {Y=120} (object): " ++ show (eval (M.fromList [('X', 4)]) (factAssertion CAssert))
  -- Hoare skip example
  let hoareSkipEg = hoareSkip (PropVar (Eq (Var 'X') (toArith 3)))
  putStrLn $ "Hoare skip example: " ++ show hoareSkipEg
  -- Hoare assignment example
  let hoareAssignmentEg = hoareAssignment 'A' (Plus (Var 'B') (S Z)) (And (PropVar (Eq (Var 'A') (S (S Z)))) (PropVar (Eq Z Z)))
  putStrLn $ "Hoare assignment example: " ++ show hoareAssignmentEg
  -- Hoare consequence example
--  putStrLn $ "Hoare consequence example: " ++ show (hoareConsequence (And True (PropVar (Eq (toArith 3) (toArith 3)))) hoareAssignmentEg (PropVar (Eq (Var 'X') (toArith 3))))
  -- Hoare sequence example
  putStrLn $ "Hoare sequence example: " ++ show (hoareSequence hoareAssignmentEg hoareSkipEg)
  -- Hoare conditional example
  let eg1 = hoareSkip (And (Not (PropVar (Eq (Var 'X') (toArith 0)))) (PropVar (Eq (toArith 0) (toArith 0))))
  let eg2 = hoareAssignment 'X' (Plus (Var 'X') (toArith 1)) (And (Not (PropVar (Eq (Var 'X') (toArith 0)))) (PropVar (Eq (toArith 0) (toArith 0))))
  putStrLn $ "Hoare conditional example: " ++ show (hoareConditional eg1 eg2)
  -- Hoare while example
--  let eg1 = HoareTriple (And (BLt (Var 'X') (toArith 10)) (BLe (Var 'X') (toArith 10))) (CAssign 'X' (Plus (Var 'X') (toArith 1))) (BLe (Var 'X') (toArith 10))
  putStrLn $ "Hoare while example: " ++ show (hoareWhile eg1)
  -- Hoare swap proof
--  let swap1 = hoareAssignment 'a' (Plus (Var 'a') (Var 'b')) (And (PropVar (Eq (Minus (Var 'a') (Var 'b')) (Var 'A'))) (PropVar (Eq (Var 'b') (Var 'B'))))
--  let swap2 = hoareAssignment 'b' (Minus (Var 'a') (Var 'b')) (And (PropVar (Eq (Var 'b') (Var 'A'))) (PropVar (Eq (Minus (Var 'a') (Var 'b')) (Var 'B'))))
--  let swap3 = hoareAssignment 'a' (Minus (Var 'a') (Var 'b')) (And (PropVar (Eq (Var 'b') (Var 'A'))) (PropVar (Eq (Var 'a') (Var 'B'))))
--  putStrLn $ intercalate "\n" ["Hoare swap proof:", show swap1, show swap2, show swap3, "-->", show $ whenRight (hoareSequence swap1 swap2) (\x -> hoareSequence x swap3)]




{-
tripleEg = hoareAssignment A (Plus (Var B) (S Z)) (And (PropVar (Eq (Var A) (S (S Z)))) (PropVar (Eq Z Z)))
eg1_p1_wff = And (PropVar (Eq (Plus (Var B) (S Z)) (S (S Z)))) (PropVar (Eq Z Z))
eg1_p2_wff = And (PropVar (Eq (Var A) (S (S Z)))) (PropVar (Eq Z Z))
eg1_p1 = ruleFantasy id eg1_p1_wff
eg1_p2 = ruleFantasy ruleSepL eg1_p2_wff
weaken = hoareConsequence eg1_p1 tripleEg eg1_p2 -- weaken postcondition

tripleEg_2 = hoareAssignment A (Plus (Var B) (S Z)) (PropVar (Eq (Var A) (S (S Z))))
eg2_p1_wff = And (PropVar (Eq (Plus (Var B) (S Z)) (S (S Z)))) (PropVar (Eq Z Z))
eg2_p2_wff = PropVar (Eq (Var A) (S (S Z)))
eg2_p1 = ruleFantasy ruleSepL eg2_p1_wff
eg2_p2 = ruleFantasy id eg2_p2_wff
strengthen = hoareConsequence eg2_p1 tripleEg_2 eg2_p2 -- strengthen postcondition

--p1' = ruleFantasy id p1_wff
--p2' = ruleFantasy id p2_wff
--strengthen = hoareConsequence p1' tripleEg p2'
{-
weaken postcondition
*Hoare> tripleEg
{<((B)+(S(0)))=(S(S(0)))>∧<(0)=(0)>} A := (B)+(S(0)); {<(A)=(S(S(0)))>∧<(0)=(0)>}
*Hoare> hoareConsequence p1 tripleEg p2
Right {<((B)+(S(0)))=(S(S(0)))>∧<(0)=(0)>} A := (B)+(S(0)); {(A)=(S(S(0)))}
-}
-}
