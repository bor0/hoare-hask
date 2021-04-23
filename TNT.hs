module TNT
  (Arith(..)
  , FOL(..)
  , applyFOLRule
  , axiom1
  , axiom2
  , axiom3
  , axiom4
  , axiom5
  , substPropCalc
  , ruleAddS
  , ruleDropS
  , ruleExistence
  , ruleGeneralize
  , ruleInduction
  , ruleInterchangeL
  , ruleInterchangeR
  , ruleSpec
  , ruleSymmetry
  , ruleTransitivity
  ) where

import Data.List ((\\), nub)
import Common
import Gentzen

{- Data defs -}

data Arith a =
  Var a
  | Z
  | S (Arith a)
  | Plus (Arith a) (Arith a)
  | Mult (Arith a) (Arith a)
  deriving (Eq)

data FOL a =
  Eq (Arith a) (Arith a)
  | ForAll a (PropCalc (FOL a))
  | Exists a (PropCalc (FOL a))
  deriving (Eq)

instance Show a => Show (Arith a) where
  show (Var a)     = show a
  show Z           = "0"
  show (S a)       = "S(" ++ show a ++ ")"
  show (Plus a b)  = "(" ++ show a ++ ")+(" ++ show b ++ ")"
  show (Mult a b)  = "(" ++ show a ++ ")*(" ++ show b ++ ")"

instance Show a => Show (FOL a) where
  show (Eq a b) = "(" ++ show a ++ ")=(" ++ show b ++ ")"
  show (ForAll x y) = "All " ++ show x ++ ":" ++ show y
  show (Exists x y) = "Exists " ++ show x ++ ":" ++ show y

{- Helper functions -}

-- | Apply FOL rule to a specific portion of a formula
-- Might be useful for some rules that may require drilling, like `ruleInterchangeL`
applyFOLRule :: Path -> (Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))) -> Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))
applyFOLRule xs f (Proof x) = Proof $ go xs (\x -> fromProof $ f (Proof x)) x
  where
  go :: Path -> (PropCalc (FOL a) -> PropCalc (FOL a)) -> PropCalc (FOL a) -> PropCalc (FOL a)
  go [] f x = f x
  go (_:xs) f (PropVar (ForAll x y)) = PropVar (ForAll x (go xs f y))
  go (_:xs) f (PropVar (Exists x y)) = PropVar (Exists x (go xs f y))
  go (_:xs) f (Not x)                = Not (go xs f x)
  go (GoLeft:xs) f (And x y)         = And (go xs f x) y
  go (GoLeft:xs) f (Imp x y)         = Imp (go xs f x) y
  go (GoLeft:xs) f (Or x y)          = Or (go xs f x) y
  go (GoRight:xs) f (And x y)        = And x (go xs f y)
  go (GoRight:xs) f (Imp x y)        = Imp x (go xs f y)
  go (GoRight:xs) f (Or x y)         = Or x (go xs f y)
  -- applyFOLRule does not work at the equational level
  go _ _ (PropVar (Eq x y))          = PropVar (Eq x y)

-- Similar to applyFOLRule, but useful for terms within formulas (used by existence rule)
applyArithRule :: Path -> (Arith a -> Arith a) -> Arith a -> Arith a
applyArithRule [] f x = f x
applyArithRule (GoLeft:xs) f (S x) = S (applyArithRule xs f x)
applyArithRule (GoLeft:xs) f (Plus x y)  = Plus (applyArithRule xs f x) y
applyArithRule (GoLeft:xs) f (Mult x y)  = Mult (applyArithRule xs f x) y
applyArithRule (GoRight:xs) f (S x) = S (applyArithRule xs f x)
applyArithRule (GoRight:xs) f (Plus x y)  = Plus x (applyArithRule xs f y)
applyArithRule (GoRight:xs) f (Mult x y)  = Mult x (applyArithRule xs f y)
applyArithRule _ _ Z = Z -- nothing to apply for 0
applyArithRule _ _ (Var x) = Var x -- nothing to apply for a variable

-- Combines applyFOLRule and applyArithRule
applyFOLArithRule :: Pos -> Path -> Path -> (Arith a -> Arith a) -> Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))
applyFOLArithRule pos path1 path2 f x = applyFOLRule path1 (\x -> Proof $ go pos (fromProof x)) x
  where
  go GoLeft (PropVar (Eq x y)) = PropVar (Eq (applyArithRule path2 f x) y)
  go GoRight (PropVar (Eq x y)) = PropVar (Eq x (applyArithRule path2 f y))
  go _ x = x

-- Get FOL terms, given specific path
getFOLTerm :: Path -> PropCalc (FOL a) -> PropCalc (FOL a)
getFOLTerm (_:xs) (PropVar (ForAll x y)) = getFOLTerm xs y
getFOLTerm (_:xs) (PropVar (Exists x y)) = getFOLTerm xs y
getFOLTerm (_:xs) (Not x)                = getFOLTerm xs x
getFOLTerm (GoLeft:xs) (And x y)         = getFOLTerm xs x
getFOLTerm (GoLeft:xs) (Imp x y)         = getFOLTerm xs x
getFOLTerm (GoLeft:xs) (Or x y)          = getFOLTerm xs x
getFOLTerm (GoRight:xs) (And x y)        = getFOLTerm xs y
getFOLTerm (GoRight:xs) (Imp x y)        = getFOLTerm xs y
getFOLTerm (GoRight:xs) (Or x y)         = getFOLTerm xs y
getFOLTerm _ x = x

-- Get Arith terms, given specific position of equation and path
getArithTerm :: (Pos, Path) -> PropCalc (FOL a) -> Arith a
getArithTerm (pos, path) (PropVar (Eq x y)) = if pos == GoLeft then go path x else go path y
  where
  go :: Path -> Arith a -> Arith a
  go (GoLeft:xs) (S x)       = go xs x
  go (GoLeft:xs) (Plus x y)  = go xs x
  go (GoLeft:xs) (Mult x y)  = go xs x
  go (GoRight:xs) (S x)      = go xs x
  go (GoRight:xs) (Plus x y) = go xs y
  go (GoRight:xs) (Mult x y) = go xs y
  go _ x = x

-- Helper wrapper
getTerm :: (Pos, Path, Path) -> PropCalc (FOL a) -> Arith a
getTerm (pos, path1, path2) x = getArithTerm (pos, path2) (getFOLTerm path1 x)

-- Substitution function for arithmetical formulas
substArith :: Eq a => Arith a -> Arith a -> Arith a -> Arith a
substArith (S q) v e = S (substArith q v e)
substArith (Plus a b) v e = Plus (substArith a v e) (substArith b v e)
substArith (Mult a b) v e = Mult (substArith a v e) (substArith b v e)
substArith x v e | x == v = e
substArith x v e = x

-- Substitution on equational level for a specific expression with another expression
substPropCalc :: Eq a => Proof (PropCalc (FOL a)) -> Arith a -> Arith a -> Proof (PropCalc (FOL a))
substPropCalc (Proof f) v e = Proof $ go f v e
  where
  go :: Eq a => PropCalc (FOL a) -> Arith a -> Arith a -> PropCalc (FOL a)
  go (PropVar (Eq a b)) v e     = PropVar (Eq (substArith a v e) (substArith b v e))
  go (PropVar (ForAll x y)) v e = PropVar (ForAll x (go y v e))
  go (PropVar (Exists x y)) v e = PropVar (Exists x (go y v e))
  go (Not x) v e                = Not (go x v e)
  go (And x y) v e              = And (go x v e) (go y v e)
  go (Or x y) v e               = Or (go x v e) (go y v e)
  go (Imp x y) v e              = Imp (go x v e) (go y v e)

-- Find bound variables in a formula
getBoundVars :: Eq a => PropCalc (FOL a) -> [a]
getBoundVars x = nub $ go x
  where
  go (PropVar (ForAll s e)) = s : go e
  go (PropVar (Exists s e)) = s : go e
  go _ = []

-- Get all variables used in an arithmetic formula
getArithVars :: Eq a => Arith a -> [a]
getArithVars x = nub $ go x
  where
  go (Var a) = [a]
  go (S x) = go x
  go (Plus a b) = go a ++ go b
  go (Mult a b) = go a ++ go b
  go _ = []

-- Get all used variables
getVars :: Eq a => PropCalc (FOL a) -> [a]
getVars x = nub $ go x
  where
  go (PropVar (ForAll s e)) = go e
  go (PropVar (Exists s e)) = go e
  go (PropVar (Eq a b)) = getArithVars a ++ getArithVars b
  go (Not x) = go x
  go (And x y) = go x ++ go y
  go (Or x y) = go x ++ go y
  go (Imp x y) = go x ++ go y

-- Get all free variables
getFreeVars :: Eq a => PropCalc (FOL a) -> [a]
getFreeVars x = getVars x \\ getBoundVars x

{- Axioms -}

-- | Peano axiom 1
-- forall a, not (S a = 0)
axiom1 a = Proof $ PropVar (ForAll a (Not (PropVar (Eq (S (Var a)) Z))))

-- | Peano axiom 2
-- forall a, (a + 0) = a
axiom2 a = Proof $ PropVar (ForAll a (PropVar (Eq (Plus (Var a) Z) (Var a))))

-- | Peano axiom 3
-- forall a, forall b, a + Sb = S(a + b)
axiom3 a b = Proof $ PropVar (ForAll a (PropVar (ForAll b (PropVar (Eq (Plus (Var a) (S (Var b))) (S (Plus (Var a) (Var b))))))))

-- | Peano axiom 4
-- forall a, (a * 0) = 0
axiom4 a = Proof $ PropVar (ForAll a (PropVar (Eq (Mult (Var a) Z) Z)))

-- | Peano axiom 5
-- forall a, forall b, a * Sb = (a * b + a)
axiom5 a b = Proof $ PropVar (ForAll a (PropVar (ForAll b (PropVar (Eq (Mult (Var a) (S (Var b))) (Plus (Mult (Var a) (Var b)) (Var a)))))))

{- Rules -}

-- | Rule of Specification
-- Suppose u is a variable which occurs inside the string x. If the string ∀u:x is a theorem, then so is x, and so are any strings made from x by replacing u, wherever it occurs, by one and the same term. (Restriction: The term which replaces u must not contain any variable that is quantified in x.)
ruleSpec :: Eq a => Proof (PropCalc (FOL a)) -> a -> Arith a -> Proof (PropCalc (FOL a))
ruleSpec (Proof f) v e = Proof $ go f v e
  where
  go :: Eq a => PropCalc (FOL a) -> a -> Arith a -> PropCalc (FOL a)
  go (PropVar (ForAll x y)) v e | x == v && not (any (`elem` getArithVars e) (getBoundVars y)) = fromProof $ substPropCalc (Proof y) (Var x) e
  go x _ _ = x

-- | Rule of Generalization
-- Suppose x is a theorem in which u, a variable, occurs free. Then ∀u:x is a theorem. (Restriction: No generalization is allowed in a fantasy on any variable which appeared free in the fantasy's premise.)
ruleGeneralize :: Eq a => Proof (PropCalc (FOL a)) -> a -> Maybe (Proof (PropCalc (FOL a))) -> Proof (PropCalc (FOL a))
ruleGeneralize (Proof f) v Nothing | v `notElem` getBoundVars f
  = Proof $ PropVar (ForAll v f)
ruleGeneralize (Proof f) v (Just premise) | v `notElem` getBoundVars f && v `notElem` getFreeVars (fromProof premise) -- fantasy vars
  = Proof $ PropVar (ForAll v f)
ruleGeneralize x _ _ = x

-- | Rule of Interchange
-- Suppose u is a variable. Then the strings ∀u:~ and ~∃u: are interchangeable anywhere inside any theorem.
ruleInterchangeL :: Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))
ruleInterchangeL (Proof (PropVar (ForAll x (Not y)))) = Proof $ Not (PropVar $ Exists x y)
ruleInterchangeL x = x

-- | Rule of Interchange
-- Suppose u is a variable. Then the strings ∀u:~ and ~∃u: are interchangeable anywhere inside any theorem.
ruleInterchangeR :: Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))
ruleInterchangeR (Proof (Not (PropVar (Exists x y)))) = Proof $ PropVar (ForAll x (Not y))
ruleInterchangeR x = x

-- | Rule of Existence
-- Suppose a term (which may contain variables as long as they are free) appears once, or multiply, in a theorem. Then any (or several, or all) of the appearances of the term may be replaced by a variable which otherwise does not occur in the theorem, and the corresponding existential quantifier must be placed in front.
ruleExistence :: Eq a => Proof (PropCalc (FOL a)) -> a -> [(Pos, Path, Path)] -> Proof (PropCalc (FOL a))
ruleExistence f v paths | allSame (map (\path -> getTerm path $ fromProof f) paths) =
  Proof $ PropVar (Exists v (fromProof (go f paths)))
  where
  go f ((pos, path1, path2):paths) =
    let newProof = applyFOLArithRule pos path1 path2 (\_ -> Var v) f
    in go newProof paths
  go x _ = x
ruleExistence x _ _ = x

-- | Rule of Symmetry
-- If r=s is a theorem, then so is s=r
ruleSymmetry :: Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))
ruleSymmetry (Proof (PropVar (Eq a b))) = Proof $ PropVar (Eq b a)
ruleSymmetry x = x

-- | Rule of Transitivity
-- If r=s and s=t are theorems, then so is r=t
ruleTransitivity :: Eq a => Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))
ruleTransitivity (Proof (PropVar (Eq a b))) (Proof (PropVar (Eq b' c))) | b == b' = Proof $ PropVar (Eq a c)
ruleTransitivity x _ = x

-- | Rule Add S
-- If r=t is a theorem, then Sr=St is a theorem.
ruleAddS :: Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))
ruleAddS (Proof (PropVar (Eq a b))) = Proof $ PropVar (Eq (S a) (S b))
ruleAddS x = x

-- | Rule Drop S
-- If Sr=St is theorem, then r=t is a theorem.
ruleDropS :: Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a))
ruleDropS (Proof (PropVar (Eq (S a) (S b)))) = Proof $ PropVar (Eq a b)
ruleDropS x = x

-- | Rule of Induction
-- Let X{u} represent a well-formed formula in which the variable u is free, and X{x/u} represent the same string, with each appearance of u replaced by x. If both ∀u:<X{u}⊃X{Su/u}> and X{0/u} are theorems, then ∀u:X{u} is also a theorem.
ruleInduction :: Eq a => Proof (PropCalc (FOL a)) -> Proof (PropCalc (FOL a)) -> Either String (Proof (PropCalc (FOL a)))
ruleInduction base (Proof ih@(PropVar (ForAll x (Imp y z)))) =
  -- in base' and conc, y is Proof y because it's an assumption
  let base' = substPropCalc (Proof y) (Var x) Z
      conc  = substPropCalc (Proof y) (Var x) (S (Var x)) in
  -- similarly, z is Proof z here
  if base' == base && conc == Proof z
  then Right $ Proof $ PropVar (ForAll x y)
  else Left "ruleInduction: Cannot construct proof"
ruleInduction x _ = Right x
