module Gentzen where

import Common
import PrettyPrinter

{- Data defs -}

data PropCalc a =
  PropVar a
  | Not (PropCalc a)
  | And (PropCalc a) (PropCalc a)
  | Or (PropCalc a) (PropCalc a)
  | Imp (PropCalc a) (PropCalc a)
  deriving (Eq, Show)

instance Pretty a => Pretty (PropCalc a) where
  pr (PropVar a) = pr a
  pr (Not a)     = "~" ++ pr a
  pr (And a b)   = "<" ++ pr a ++ "> /\\ <" ++ pr b ++ ">"
  pr (Or a b)    = "<" ++ pr a ++ "> \\/ <" ++ pr b ++ ">"
  pr (Imp a b)   = "<" ++ pr a ++ "> -> <" ++ pr b ++ ">"

{- Helper functions -}

-- | Apply prop rule to a specific portion of a formula
-- Might be useful for some rules that may require drilling
applyPropRule :: Path -> (Proof (PropCalc a) -> Proof (PropCalc a)) -> Proof (PropCalc a) -> Proof (PropCalc a)
applyPropRule xs f (Proof x) = Proof $ go xs (\x -> fromProof $ f (Proof x)) x
  where
  go :: Path -> (PropCalc a -> PropCalc a) -> PropCalc a -> PropCalc a
  go (GoLeft:xs) f (Not x) = Not (go xs f x)
  go (GoLeft:xs) f (And x y) = And (go xs f x) y
  go (GoLeft:xs) f (Or x y) = Or (go xs f x) y
  go (GoLeft:xs) f (Imp x y) = Imp (go xs f x) y
  go (GoRight:xs) f (Not x) = Not (go xs f x)
  go (GoRight:xs) f (And x y) = And x (go xs f y)
  go (GoRight:xs) f (Or x y) = Or x (go xs f y)
  go (GoRight:xs) f (Imp x y) = Imp x (go xs f y)
  go _ f x = f x

{- Rules -}

-- | Joining Rule
-- If x and y are theorems, then <x∧y> is a theorem.
ruleJoin :: Proof (PropCalc a) -> Proof (PropCalc a) -> Proof (PropCalc a)
ruleJoin (Proof x) (Proof y) = Proof $ And x y

-- | Sep Rule
-- If <x∧y> is a theorem, then both x and y are theorems.
ruleSepL :: Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleSepL (Proof (And x y)) = Right $ Proof x
ruleSepL _ = Left "ruleSepL: Cannot construct proof"

-- | Sep Rule
-- If <x∧y> is a theorem, then both x and y are theorems.
ruleSepR :: Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleSepR (Proof (And x y)) = Right $ Proof y
ruleSepR _ = Left "ruleSepL: Cannot construct proof"

-- | Double-Tilde Rule
-- The string ~~ can be deleted from any theorem. It can also be inserted into any theorem, provided that the resulting string is itself well-formed
ruleDoubleTildeIntro :: Proof (PropCalc a) -> Proof (PropCalc a)
ruleDoubleTildeIntro (Proof x) = Proof $ Not (Not x)

-- | Double-Tilde Rule
-- The string ~~ can be deleted from any theorem. It can also be inserted into any theorem, provided that the resulting string is itself well-formed
ruleDoubleTildeElim :: Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleDoubleTildeElim (Proof (Not (Not x))) = Right $ Proof x
ruleDoubleTildeElim _ = Left "ruleDoubleTildeElim: Cannot construct proof"

-- | Fantasy Rule (Carry over)
-- If x were a theorem, y would be a theorem.
-- Additionally, inside a fantasy, any theorem from the "reality" one level higher can be brought in and used.
-- Imp intro accepts a rule and an assumption (simply a well-formed formula, not necessarily proven)
-- Our data types are constructed such that all formulas are well-formed
ruleFantasy :: (Proof (PropCalc a) -> Proof (PropCalc a)) -> PropCalc a -> Proof (PropCalc a)
ruleFantasy f x = Proof $ Imp x $ fromProof (f (Proof x))

-- | Rule of Detachment
-- If x and <x⊃y> are both theorems, then y is a theorem.
ruleDetachment :: Eq a => Proof (PropCalc a) -> Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleDetachment (Proof x) (Proof (Imp x' y)) | x == x' = Right $ Proof y
ruleDetachment _ _ = Left "ruleDetachment: Cannot construct proof"

-- | Contrapositive Rule
-- <x⊃y> and <~y⊃~x> are interchangeable.
ruleContra :: Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleContra (Proof (Imp (Not y) (Not x))) = Right $ Proof $ Imp x y
ruleContra (Proof (Imp x y)) = Right $ Proof $ Imp (Not y) (Not x)
ruleContra _ = Left "ruleContra: Cannot construct proof"

-- | De Morgan's Rule
-- <~x∧~y> and ~<x∨y> are interchangeable.
ruleDeMorgan :: Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleDeMorgan (Proof (And (Not x) (Not y))) = Right $ Proof $ Not (Or x y)
ruleDeMorgan (Proof (Not (Or x y))) = Right $ Proof $ And (Not x) (Not y)
ruleDeMorgan _ = Left "ruleDeMorgan: Cannot construct proof"

-- | Switcheroo Rule
-- <x∨y> and <~x⊃y> are interchangeable.
ruleSwitcheroo :: Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleSwitcheroo (Proof (Or x y)) = Right $ Proof $ Imp (Not x) y
ruleSwitcheroo (Proof (Imp (Not x) y)) = Right $ Proof $ Or x y
ruleSwitcheroo _ = Left "ruleSwitcheroo: Cannot construct proof"
