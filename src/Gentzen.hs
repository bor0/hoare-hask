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
  prPrec x (PropVar a) = prPrec x a
  prPrec q (Not formula) = prParen (q > 3) ("<",">") $
    "~" ++ prPrec 3 formula
  prPrec q (And lhs rhs) = prParen (q > 2) ("<",">") $
    prPrec 3 lhs ++ " /\\ " ++ prPrec 2 rhs
  prPrec q (Or lhs rhs)  = prParen (q > 1) ("<",">") $
    prPrec 2 lhs ++ " \\/ " ++ prPrec 1 rhs
  prPrec q (Imp lhs rhs) = prParen (q > 0) ("<",">") $
    prPrec 1 lhs ++ " -> " ++ prPrec 0 rhs

{- Helper functions -}

-- | Apply prop rule to a specific portion of a formula
-- Might be useful for some rules that may require drilling
applyPropRule :: Path -> (Proof (PropCalc a) -> Either String (Proof (PropCalc a))) -> Proof (PropCalc a) -> Either String (Proof (PropCalc a))
applyPropRule xs f (Proof x) = go xs f x
  where
  go :: Path -> (Proof (PropCalc a) -> Either String (Proof (PropCalc a))) -> PropCalc a -> Either String (Proof (PropCalc a))
  go (_:xs) f (Not x)         = go xs f x >>= \prfx -> Right $ Proof $ Not (fromProof prfx)
  go (GoLeft:xs) f (And x y)  = go xs f x >>= \prfx -> Right $ Proof $ And (fromProof prfx) y
  go (GoLeft:xs) f (Or x y)   = go xs f x >>= \prfx -> Right $ Proof $ Or (fromProof prfx) y
  go (GoLeft:xs) f (Imp x y)  = go xs f x >>= \prfx -> Right $ Proof $ Imp (fromProof prfx) y
  go (GoRight:xs) f (And x y) = go xs f y >>= \prfy -> Right $ Proof $ And x (fromProof prfy)
  go (GoRight:xs) f (Or x y)  = go xs f y >>= \prfy -> Right $ Proof $ Or x (fromProof prfy)
  go (GoRight:xs) f (Imp x y) = go xs f y >>= \prfy -> Right $ Proof $ Imp x (fromProof prfy)
  go _ f x = f (Proof x)

{- Rules -}

-- | Joining Rule
-- If x and y are theorems, then <x∧y> is a theorem.
ruleJoin :: Proof (PropCalc a) -> Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleJoin (Proof x) (Proof y) = Right $ Proof $ And x y

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
ruleDoubleTildeIntro :: Proof (PropCalc a) -> Either String (Proof (PropCalc a))
ruleDoubleTildeIntro (Proof x) = Right $ Proof $ Not (Not x)

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
ruleFantasy :: PropCalc a -> (Proof (PropCalc a) -> Either String (Proof (PropCalc a))) -> Either String (Proof (PropCalc a))
ruleFantasy x f = f (Proof x) >>= \prfx -> Right $ Proof $ Imp x (fromProof prfx)

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
