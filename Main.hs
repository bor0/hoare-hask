module Main where

import Arithmetic
import Boolean
import Command
import Eval
import Utils
import Hoare
import qualified Data.Map as M

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
  let hoareSkipEg = hoareSkip CSkip (BEq (AId 'X') (ANum 3))
  putStrLn $ "Hoare skip example: " ++ show hoareSkipEg
  -- Hoare assignment example
  let hoareAssignmentEg = hoareAssignment (CAssign 'X' (ANum 3)) (BEq (AId 'X') (ANum 3))
  putStrLn $ "Hoare assignment example: " ++ show hoareAssignmentEg
  -- Hoare sequence example
  putStrLn $ "Hoare sequence example: " ++ show (whenRight hoareAssignmentEg (\eg1 -> whenRight hoareSkipEg (\eg2 -> hoareSequence eg1 eg2)))
  -- Hoare conditional example
  let b = BEq (AId 'X') (ANum 0)
  let p = BLe (AId 'X') (ANum 10)
  let q = BEq (AId 'X') (ANum 3)
  let c1 = CSequence (CAssign 'X' (ANum 1)) (CAssign 'X' (ANum 3))
  let c2 = CAssign 'X' (ANum 3)
  putStrLn $ "Hoare conditional example: " ++ show (hoareConditional (HoareTriple (BAnd b p) c1 q) (HoareTriple (BAnd (BNot b) p) c2 q))
  -- Hoare while example
  putStrLn $ "Hoare while example: " ++ show (hoareWhile (HoareTriple (BAnd b p) c2 p))
