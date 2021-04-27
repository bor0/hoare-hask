module ExampleCommon where

import PrettyPrinter

{- Example variables -}
data Vars = A | B | C | D deriving (Eq, Ord, Show)

instance Pretty Vars where
  pr = show
