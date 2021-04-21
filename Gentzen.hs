module Gentzen where

import Common

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
ruleSepL :: Proof (PropCalc a) -> Proof (PropCalc a)
ruleSepL (Proof (And x y)) = Proof x
ruleSepL x = x

-- | Sep Rule
-- If <x∧y> is a theorem, then both x and y are theorems.
ruleSepR :: Proof (PropCalc a) -> Proof (PropCalc a)
ruleSepR (Proof (And x y)) = Proof y
ruleSepR x = x

-- | Double-Tilde Rule
-- The string ~~ can be deleted from any theorem. It can also be inserted into any theorem, provided that the resulting string is itself well-formed
ruleDoubleTildeIntro :: Proof (PropCalc a) -> Proof (PropCalc a)
ruleDoubleTildeIntro (Proof x) = Proof $ Not (Not x)

-- | Double-Tilde Rule
-- The string ~~ can be deleted from any theorem. It can also be inserted into any theorem, provided that the resulting string is itself well-formed
ruleDoubleTildeElim :: Proof (PropCalc a) -> Proof (PropCalc a)
ruleDoubleTildeElim (Proof (Not (Not x))) = Proof x
ruleDoubleTildeElim x = x

-- | Fantasy Rule (Carry over)
-- If x were a theorem, y would be a theorem.
-- Additionally, inside a fantasy, any theorem from the "reality" one level higher can be brought in and used.
-- Imp intro accepts a rule and an assumption (simply a well-formed formula, not necessarily proven)
-- Our data types are constructed such that all formulas are well-formed
ruleFantasy :: (Proof (PropCalc a) -> Proof (PropCalc a)) -> PropCalc a -> Proof (PropCalc a)
ruleFantasy f x = Proof $ Imp x $ fromProof (f (Proof x))

-- | Rule of Detachment
-- If x and <x⊃y> are both theorems, then y is a theorem.
ruleDetachment :: Eq a => Proof (PropCalc a) -> Proof (PropCalc a) -> Proof (PropCalc a)
ruleDetachment (Proof x) (Proof (Imp x' y)) | x == x' = Proof y
ruleDetachment _ _ = error "ruleDetachment: Not applicable"

-- | Contrapositive Rule
-- <x⊃y> and <~y⊃~x> are interchangeable.
ruleContra :: Proof (PropCalc a) -> Proof (PropCalc a)
ruleContra (Proof (Imp (Not y) (Not x))) = Proof $ Imp x y
ruleContra (Proof (Imp x y)) = Proof $ Imp (Not y) (Not x)
ruleContra x = x

-- | De Morgan's Rule
-- <~x∧~y> and ~<x∨y> are interchangeable.
ruleDeMorgan :: Proof (PropCalc a) -> Proof (PropCalc a)
ruleDeMorgan (Proof (And (Not x) (Not y))) = Proof $ Not (Or x y)
ruleDeMorgan (Proof (Not (Or x y))) = Proof $ And (Not x) (Not y)
ruleDeMorgan x = x

-- | Switcheroo Rule
-- <x∨y> and <~x⊃y> are interchangeable.
ruleSwitcheroo :: Proof (PropCalc a) -> Proof (PropCalc a)
ruleSwitcheroo (Proof (Or x y)) = Proof $ Imp (Not x) y
ruleSwitcheroo (Proof (Imp (Not x) y)) = Proof $ Or x y
ruleSwitcheroo x = x
