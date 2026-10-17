-- Level.hs -- universe levels and level constraints.
--
-- Levels are the terms of a join-semilattice with an inflationary
-- endomorphism (bcde.pdf, section 4):  l ::= a | l+ | l \/ m .  There is no
-- level 0 for the user.  Internally there is one distinguished variable
-- "0" with  0 <= a  for every a: it is the level of the small data types
-- (bcde.pdf: N : U_l for every l), and nothing else.
--
-- A theory is a finite presentation (level variables, constraints).  The
-- uniform word problem and loop checking are decided as in Bezem-Coquand,
-- "Loop-checking and the uniform word problem for join-semilattices with
-- an inflationary endomorphism" (TCS 913, 2022): constraints become Horn
-- clauses over atoms x+k, closed under shifting upwards, and  A -> b  is
-- decided by computing the least model above A by forward reasoning.
--
-- The cap.  In a loop-free theory the least model above a finite f is
-- finite, and no value exceeds  max f + |V| * maxgain : if values above
-- max f had a gap of length maxgain, lowering every variable above the gap
-- by one would give a smaller model.  So forward reasoning that passes the
-- cap has found a loop, and the iteration always terminates.

module Level
  ( LName, Lvl(..), lvar, lsuc, lmax, lzero, latoms, lvars, lsubst, showLvl
  , Cstr(..), Theory, emptyTheory, addVar, addCstr, thLoop, thVars
  , leq, leqs, eqLvl, validCstr
  ) where

import Data.List (sortBy, nub)

type LName = String

-- a level in normal form: a join of atoms x+k, one atom per variable
-- (the largest offset), sorted by variable.  Never empty.
newtype Lvl = Lvl [(LName, Int)]
  deriving (Eq, Show)

norm :: [(LName, Int)] -> Lvl
norm as = Lvl (drop0 (merge (sortBy (\a b -> compare (fst a) (fst b)) as)))
 where
  merge ((x, k) : (y, j) : rest)
    | x == y    = merge ((x, max k j) : rest)
    | otherwise = (x, k) : merge ((y, j) : rest)
  merge r = r
  -- 0+k is below any other atom with offset >= k
  drop0 r = case [ k | ("0", k) <- r ] of
    [k] | any (\(x, j) -> x /= "0" && j >= k) r -> filter ((/= "0") . fst) r
    _ -> r

lvar :: LName -> Lvl
lvar x = Lvl [(x, 0)]

lzero :: Lvl
lzero = Lvl [("0", 0)]

lsuc :: Lvl -> Lvl
lsuc (Lvl as) = Lvl [ (x, k + 1) | (x, k) <- as ]

lmax :: Lvl -> Lvl -> Lvl
lmax (Lvl a) (Lvl b) = norm (a ++ b)

latoms :: Lvl -> [(LName, Int)]
latoms (Lvl as) = as

lvars :: Lvl -> [LName]
lvars (Lvl as) = [ x | (x, _) <- as, x /= "0" ]

-- substitute levels for variables
lsubst :: (LName -> Lvl) -> Lvl -> Lvl
lsubst f (Lvl as) = foldr1 lmax [ shift k (if x == "0" then lzero else f x) | (x, k) <- as ]
 where shift k (Lvl bs) = Lvl [ (y, j + k) | (y, j) <- bs ]

showLvl :: Lvl -> String
showLvl (Lvl as) = case as of
  [a] -> atom a
  _   -> "(" ++ foldr1 (\a b -> a ++ " \\/ " ++ b) (map atom as) ++ ")"
 where atom (x, k) = x ++ replicate k '+'

------------------------------------------------------------------------
-- Constraints and theories

data Cstr = CEq Lvl Lvl | CLe Lvl Lvl | CLt Lvl Lvl
  deriving (Eq, Show)

type Atom   = (LName, Int)
type Clause = ([Atom], Atom)          -- a non-empty body implies an atom

data Theory = Theory { thVars :: [LName], thCl :: [Clause], thLoop :: Bool }

emptyTheory :: Theory
emptyTheory = Theory ["0"] [] False

addVar :: LName -> Theory -> Theory
addVar v th
  | v `elem` thVars th = th
  | otherwise = th { thVars = v : thVars th, thCl = ([(v, 0)], ("0", 0)) : thCl th }

-- l <= m  is  m \/ l = m : every atom of l follows from the atoms of m
leClauses :: Lvl -> Lvl -> [Clause]
leClauses l m = [ (latoms m, b) | b <- latoms l ]

cstrClauses :: Cstr -> [Clause]
cstrClauses (CEq l m) = leClauses l m ++ leClauses m l
cstrClauses (CLe l m) = leClauses l m
cstrClauses (CLt l m) = leClauses (lsuc l) m

addCstr :: Cstr -> Theory -> Theory
addCstr c th0 = th { thLoop = thLoop th0 || hasLoop th }
 where
  vs  = nub (concatMap lvars (cstrLvls c))
  th1 = foldr addVar th0 vs
  th  = th1 { thCl = cstrClauses c ++ thCl th1 }

cstrLvls :: Cstr -> [Lvl]
cstrLvls (CEq l m) = [l, m]
cstrLvls (CLe l m) = [l, m]
cstrLvls (CLt l m) = [l, m]

------------------------------------------------------------------------
-- Forward reasoning.  A model is a function  V -> {-1} u N : the value k
-- stands for the downward closed set of atoms v+0 .. v+k, and -1 for the
-- empty set.  Returns Nothing when the cap is passed (a loop).

type Model = [(LName, Int)]

val :: Model -> LName -> Int
val f x = maybe (-1) id (lookup x f)

maxGain :: [Clause] -> Int
maxGain cs = maximum (1 : [ l - minimum (map snd body) | (body, (_, l)) <- cs ])

leastModel :: Theory -> Model -> Maybe Model
leastModel th f0 = go f0
 where
  cs   = thCl th
  vs   = nub (thVars th ++ map fst f0)
  cap  = maximum (0 : map snd f0 ++ [ k | (b, _) <- cs, (_, k) <- b ])
         + (length vs + 1) * maxGain cs + 1
  go f = case [ (y, n) | (body, (y, l)) <- cs
                       , let k0 = minimum [ val f x - k | (x, k) <- body ]
                       , k0 >= 0, let n = l + k0, n > val f y ] of
    [] -> Just f
    new | any ((> cap) . snd) new -> Nothing
        | otherwise -> go (foldl raise f new)
  raise f (y, n) = (y, max n (val f y)) : filter ((/= y) . fst) f

hasLoop :: Theory -> Bool
hasLoop th = case leastModel th [ (v, m) | v <- thVars th ] of
  Nothing -> True
  Just _  -> False
 where m = maximum (0 : [ k | (b, _) <- thCl th, (_, k) <- b ])

-- the theory proves  l <= m .  A theory with a loop proves everything:
-- the context collapses (bcde.pdf, Appendix C, Gonthier's rule).
leq :: Theory -> Lvl -> Lvl -> Bool
leq th l m
  | thLoop th = True
  | otherwise = case leastModel th (fromAtoms (latoms m)) of
      Nothing -> True
      Just g  -> all (\(y, k) -> val g y >= k) (latoms l)
 where fromAtoms as = [ (x, maximum [ k | (y, k) <- as, y == x ]) | x <- nub (map fst as) ]

leqs :: Theory -> [(Lvl, Lvl)] -> Bool
leqs th = all (uncurry (leq th))

eqLvl :: Theory -> Lvl -> Lvl -> Bool
eqLvl th l m = l == m || (leq th l m && leq th m l)

validCstr :: Theory -> Cstr -> Bool
validCstr th (CEq l m) = eqLvl th l m
validCstr th (CLe l m) = leq th l m
validCstr th (CLt l m) = leq th (lsuc l) m
