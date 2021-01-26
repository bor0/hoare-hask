module Command where

import Arithmetic
import Boolean

data Command =
  CSkip
  | CAssign Char Aexp
  | CSequence Command Command
  | CIfElse Bexp Command Command
  | CWhile Bexp Command
  | CAssert Bexp Command Bexp

instance Show Command where
  show CSkip           = ";"
  show (CAssign x y)   = [x] ++ " := " ++ show y ++ ";"
  show (CSequence x y) = show x ++ " " ++ show y
  show (CIfElse x y z) = "(If (" ++ show x ++ ") Then (" ++ show y ++ ") Else (" ++ show z ++ "));"
  show (CWhile x y)    = "(While (" ++ show x ++ ") Do {" ++ show y ++ "});"
  show (CAssert x y z) = "(Assert {" ++ show x ++ "} (" ++ show y ++ ") {" ++ show z ++ "});"
