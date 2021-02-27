module Main where

import Arithmetic
import Boolean
import Command
import Eval
import Utils
import Hoare
import qualified Data.Map as M

import Data.List (intercalate)

-- Calculate factorial of X
factX =
  -- Z := X
  let l1 = CAssign 'Z' $ AId 'X'
  -- Y := 1
      l2 = CAssign 'Y' (ANum 1)
  -- while (~Z = 0)
      l3 = CWhile (BNot (BEq (AId 'Z') (ANum 0))) (CSequence l4 l5)
     -- Y := Y * Z
      l4 = CAssign 'Y' (AMult (AId 'Y') (AId 'Z'))
     -- Z := Z - 1
      l5 = CAssign 'Z' (AMinus (AId 'Z') (ANum 1))
  in CSequence l1 (CSequence l2 l3)

factAssertion f = f
  (BEq (ANum 5) (AId 'X'))
  factX
  (BEq (ANum 120) (AId 'Y'))

main = do
  -- Arithmetic language example
  let expr = APlus (AId 'X') (ANum 5) in putStrLn $ show expr ++ " = " ++ show (aeval (M.fromList [('X', 5)]) expr)
  let expr = APlus (AId 'X') (ANum 5) in putStrLn $ "Optimize (context-less) " ++ show expr ++ " = " ++ show (aoptimize expr)
  let expr = APlus (ANum 2) (ANum 5) in putStrLn $ "Optimize (context-less) " ++ show expr ++ " = " ++ show (aoptimize expr)
  -- Boolean language example
  let expr = BEq (AId 'X') (ANum 5) in putStrLn $ show expr ++ " = " ++ show (beval (M.fromList [('X', 5)]) expr)
  let expr = BNot BTrue in putStrLn $ "Optimize (context-less) " ++ show expr ++ " = " ++ show (boptimize expr)
  -- Eval (run program) example
  putStrLn $ "Calculate the factorial of 5: " ++ show (eval (M.fromList [('X', 5)]) factX)
  -- Assertion example (meta)
  putStrLn $ "(PASS) Assert {X=5} factX {Y=120} (meta): " ++ show (factAssertion (assert (M.fromList [('X', 5)])))
  putStrLn $ "(FAIL) Assert {X=5} factX {Y=120} (meta): " ++ show (factAssertion (assert (M.fromList [('X', 4)])))
  -- Assertion example (object)
  putStrLn $ "(PASS) Assert {X=5} factX {Y=120} (object): " ++ show (eval (M.fromList [('X', 5)]) (factAssertion CAssert))
  putStrLn $ "(FAIL) Assert {X=4} factX {Y=120} (object): " ++ show (eval (M.fromList [('X', 4)]) (factAssertion CAssert))
  -- Hoare skip example
  let hoareSkipEg = hoareSkip (BEq (AId 'X') (ANum 3))
  putStrLn $ "Hoare skip example: " ++ show hoareSkipEg
  -- Hoare assignment example
  let hoareAssignmentEg = hoareAssignment 'X' (ANum 3) (BEq (AId 'X') (ANum 3))
  putStrLn $ "Hoare assignment example: " ++ show hoareAssignmentEg
  -- Hoare consequence example
  putStrLn $ "Hoare consequence example: " ++ show (hoareConsequence (BAnd BTrue (BEq (ANum 3) (ANum 3))) hoareAssignmentEg (BEq (AId 'X') (ANum 3)))
  -- Hoare sequence example
  putStrLn $ "Hoare sequence example: " ++ show (hoareSequence hoareAssignmentEg hoareSkipEg)
  -- Hoare conditional example
  let eg1 = hoareSkip (BAnd (BNot (BEq (AId 'X') (ANum 0))) (BEq (ANum 0) (ANum 0)))
  let eg2 = hoareAssignment 'X' (APlus (AId 'X') (ANum 1)) (BAnd (BNot (BEq (AId 'X') (ANum 0))) (BEq (ANum 0) (ANum 0)))
  putStrLn $ "Hoare conditional example: " ++ show (hoareConditional eg1 eg2)
  -- Hoare swap proof
  let swap1 = hoareAssignment 'a' (APlus (AId 'a') (AId 'b')) (BAnd (BEq (AMinus (AId 'a') (AId 'b')) (AId 'A')) (BEq (AId 'b') (AId 'B')))
  let swap2 = hoareAssignment 'b' (AMinus (AId 'a') (AId 'b')) (BAnd (BEq (AId 'b') (AId 'A')) (BEq (AMinus (AId 'a') (AId 'b')) (AId 'B')))
  let swap3 = hoareAssignment 'a' (AMinus (AId 'a') (AId 'b')) (BAnd (BEq (AId 'b') (AId 'A')) (BEq (AId 'a') (AId 'B')))
  putStrLn $ intercalate "\n" ["Hoare swap proof:", show swap1, show swap2, show swap3, "-->", show $ whenRight (hoareSequence swap1 swap2) (\x -> hoareSequence x swap3)]
