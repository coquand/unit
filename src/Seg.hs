-- Seg.hs -- a dependent type theory checked in a context of UNIT
-- declarations, with AUTOMATH/Wang segments as the module system and the
-- universe system of bcde.pdf (BCDE4: Russell, cumulative, level- and
-- constraint-indexed products).
--
-- Lineage: the core is mtt (mTT10's calculus of definitions: blocks in the
-- environment, labelled sums, split).  What is new:
--
--  * UNITS.  A program, a module body and a let are lists of units:
--        x : A          a parameter (at top level: a primitive notion)
--        x : A = e      a definition (data and split are definitions)
--        level a        a level variable
--        constraint c   a level constraint
--        module M {..}  a segment; its parameters are its body-less units
--        module N = M[..]   an instance
--    Checking threads a context of units (final.pdf, chapter 3, generalised
--    to levels and constraints), and the environment is built from it.
--
--  * SEGMENTS SHARE.  An instance  M[args]  only binds M's parameters in an
--    environment.  A member  f  keeps ONE identity -- its qualified name --
--    and its value is glued: the name, the values of the parameters it
--    depends on, and a lazy unfolding.  Two occurrences of  M[fe,ua].f  are
--    compared by name and arguments before anything is unfolded.  This is
--    what Agda's module application (a copy per instance) cannot do; see
--    ~/DOMAIN/MODEL/modules.tex.
--
--  * THE LOCK is a property of the checking run (Wang): a set of qualified
--    names that conversion and weak-head reduction do not unfold.  Values
--    are computed lock-agnostically; only  whnf  consults the strategy, so a
--    lock placed AFTER a module still applies to that module's members.
--
--  * UNIVERSES.  U l : U l+ , cumulative (A : U l, l <= m  gives  A : U m),
--    Pi/Sigma/records/Id in U l when their parts are; level products
--    [a]A  (<a> t,  t @l) and constraint products  [psi]A  (introduced and
--    discharged silently: [psi]A = A when psi is valid), both LARGE types,
--    in no universe.  Validity and loops by Bezem-Coquand (Level.hs); a
--    context with a loop collapses (Gonthier's rule): everything converts.
--
-- Haskell2010, base only, no type classes of our own.

module Seg where

import Level
import Data.Maybe (fromMaybe)
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import System.Environment (lookupEnv)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type Name = String
type Id   = String                   -- the unique identity of a declaration

-- the locked constants at a point (the lock strategy): a set, since whnf
-- tests membership at every unfolding
type Locks = Set.Set Id

------------------------------------------------------------------------
-- 1.  Syntax

data Lv = LV Name | LSuc Lv | LMax Lv Lv | LZero
  deriving (Eq, Show)

data Rel = REq | RLe | RLt
  deriving (Eq, Show)

data Cs = Cs Lv Rel Lv
  deriving (Eq, Show)

type Tel = [(Name, Exp)]

data Arg = ATm Exp | ALv Lv
  deriving (Eq, Show)

-- a module expression:  M ,  e.N ,  e[args]
data MExp = MVar Name | MSub MExp Name | MApp MExp [Arg]
  deriving (Eq, Show)

data Directive = DNormal Exp | DType Exp | DFails [Unit] | DConv Exp Exp
  deriving (Eq, Show)

data Unit
  = UDef  Id Name Exp Exp [Name]     -- id, name, type, body, dependencies
  | UPar  Id Name Exp                -- a parameter / primitive notion
  | ULvl  Name                       -- a level variable
  | UCstr [Cs]                       -- constraints
  | UMod  Id Name [Unit] [Name]      -- a segment, its dependencies
  | UInst Id Name MExp               -- module N = M[args]
  | ULock [Id]                       -- the lock strategy from here on
  | UDir  Directive
  deriving (Eq, Show)

unitName :: Unit -> Name
unitName u = case u of
  UDef _ x _ _ _ -> x
  UPar _ x _     -> x
  ULvl x         -> x
  UMod _ x _ _   -> x
  UInst _ x _    -> x
  _              -> ""

-- the dependencies of a definition: the variables (lambda-bound, pattern
-- variables, parameters, level variables) it mentions, directly or through
-- other definitions.  Computed statically by the resolver.  They are the
-- DYNAMIC part of the constant (bengt.pdf slides 31-33): two occurrences of
-- one constant are equal when these have equal values.

data Exp
  = U Lv
  | Var Name
  | App Exp Exp
  | Lam Name Exp
  | Pi Name Exp Exp
  | Let [Unit] Exp
  | Sum Id [Name] [(Name, Tel)]              -- d_L, its dependencies, labels
  | Con Name [Exp]
  | Split Id [Name] [(Name, ([Name], Exp))]  -- f_B, its dependencies, branches
  | Sig Name Exp Exp
  | Pair Exp Exp
  | Fst Exp
  | Snd Exp
  | Rec Tel                                  -- sig { l : A ; .. }
  | Struct [(Name, Exp)]                     -- struct { l = e ; .. }
  | Proj Exp Name                            -- e.l
  | Id Exp Exp Exp
  | Refl Exp
  | IdJ Exp Exp Exp Exp Exp Exp              -- idJ A a C d b p
  | LPi Name Exp                             -- [a] A
  | LLam Name Exp                            -- <a> t
  | LApp Exp Lv                              -- t @l
  | CPi [Cs] Exp                             -- [psi] A
  | Acc MExp Name                            -- M[args].x
  | SegT MExp [(Name, Arg)]                  -- a segment as a type, some
                                             -- parameters fixed (Arend's
                                             -- class extension C { | f => e })
  | New MExp                                 -- new M[args] : an element
  | ProjU Exp Name                           -- e.l with e not a variable: the
                                             -- filling pass resolves a member
                                             -- of a segment by eta (below)
  | Named Id [Name] Exp                      -- a Sigma or sig occurrence with
                                             -- its internal name and the
                                             -- variables it depends on
  | Hole                                     -- a hidden argument, filled
                                             -- before the core sees the term
  deriving (Eq, Show)

------------------------------------------------------------------------
-- 2.  Values

data Env
  = ENil
  | EVar Env Name Val
  | ELvl Env Name Lvl
  | EDef Env [Unit] [(Name, Ent)] QFrag     -- a mutual group, evaluated once,
                                           -- with its part of the naming
                                           -- table (for quoting), built once

data Ent = EVal Val | EMod Mod

-- a segment: its units, the environment where it is declared, its
-- identity (id and the values of what it depends on), and, once all its
-- parameters are given, the instance environment
data Mod = Mod { modId :: Id, modDyn :: [Val], modUnits :: [Unit], modEnv :: Env
               , modInst :: Maybe Env }

data Clos  = Clos Name Exp Env
data LClos = LClos Name Exp Env

data Elim = EApp Val | EFst | ESnd | EProj Name | ELApp Lvl

-- Sigma and record types are compared BY NAME (Half, Cederquist 7.1;
-- Gofer's is_intensional): the internal name of the occurrence, the names
-- and the values of the variables it depends on.  Never by their fields.
type SName = Maybe (Id, [Name], [Val])

data Val
  = VU Lvl
  | VGen Int                                -- a generic variable
  | VConst Id [Val]                         -- a rigid constant (parameter, PN)
  | VDef Id [Val] [Elim] Val [(Name, Val)]  -- glued: name, dynamic part,
                                            -- spine (reversed), unfolding, and
                                            -- the parameters of the enclosing
                                            -- segments (for quoting only:
                                            -- conversion ignores them)
  | VLvl Lvl                                -- a level, inside dynamic parts
  | VApp Val Val
  | VLam Clos
  | VPi Val Clos
  | VCon Name [Val]
  | VSum Id [Val] [(Name, Tel)] Env
  | VSplit Id [Val] [(Name, ([Name], Exp))] Env
  | VSig SName Val Clos                     -- SName: the internal name
                                            -- of its occurrence, if any
  | VPair Val Val
  | VFst Val
  | VSnd Val
  | VRec SName Tel Env
  | VStruct [(Name, Val)]
  | VProj Val Name
  | VId Val Val Val
  | VRefl Val
  | VIdJ Val Val Val Val Val Val
  | VLPi LClos
  | VLLam LClos
  | VLApp Val Lvl
  | VCPi [Cstr] Val
  | VSegT Mod [(Name, Val)]                 -- a segment type, fixed fields
  | VInst Mod Env                           -- an element: an instance
  | VNamedE Id [Val] Val                    -- an element written as  new M[..]
                                            -- or struct {..}: its internal name
                                            -- and dynamic part (Gofer: a struct
                                            -- is compared by name, never by
                                            -- its fields), and the element

------------------------------------------------------------------------
-- 3.  Evaluation (lock-agnostic)

evalLv :: Env -> Lv -> Lvl
evalLv r l = case l of
  LV x     -> lookupLvl r x
  LSuc m   -> lsuc (evalLv r m)
  LMax a b -> lmax (evalLv r a) (evalLv r b)
  LZero    -> lzero

evalCs :: Env -> Cs -> Cstr
evalCs r (Cs l rel m) = case rel of
  REq -> CEq (evalLv r l) (evalLv r m)
  RLe -> CLe (evalLv r l) (evalLv r m)
  RLt -> CLt (evalLv r l) (evalLv r m)

eval :: Env -> Exp -> Val
eval r e = case e of
  U l          -> VU (evalLv r l)
  Var x        -> lookupVal r x
  App a b      -> app (eval r a) (eval r b)
  Lam x b      -> VLam (Clos x b r)
  Pi x a b     -> VPi (eval r a) (Clos x b r)
  Let us b     -> eval (mkGroup r us) b
  Sum t ds cs  -> VSum t (map (lookupDyn r) ds) cs r
  Con c as     -> VCon c (map (eval r) as)
  Split t ds bs -> VSplit t (map (lookupDyn r) ds) bs r
  Sig x a b    -> VSig Nothing (eval r a) (Clos x b r)
  Pair a b     -> VPair (eval r a) (eval r b)
  Fst a        -> vfst (eval r a)
  Snd a        -> vsnd (eval r a)
  Rec tel      -> VRec Nothing tel r
  Named i ds e -> let nm = Just (i, ds, map (lookupDyn r) ds)
                  in case eval r e of
                       VSig _ a f  -> VSig nm a f
                       VRec _ t r' -> VRec nm t r'
                       v@(VInst{})   -> VNamedE i (map (lookupDyn r) ds) v
                       v@(VStruct _) -> VNamedE i (map (lookupDyn r) ds) v
                       v           -> v
  Struct fs    -> VStruct [ (l, eval r a) | (l, a) <- fs ]
  Proj a l     -> vproj (eval r a) l
  Id a x y     -> VId (eval r a) (eval r x) (eval r y)
  Refl a       -> VRefl (eval r a)
  IdJ a x c d y p ->
    vidj (eval r a) (eval r x) (eval r c) (eval r d) (eval r y) (eval r p)
  LPi x a      -> VLPi (LClos x a r)
  LLam x a     -> VLLam (LClos x a r)
  LApp a l     -> lapp (eval r a) (evalLv r l)
  CPi cs a     -> VCPi (map (evalCs r) cs) (eval r a)
  Acc m x      -> lookupVal (instOf (evalMod r m)) x
  SegT m fs    -> VSegT (evalMod r m) [ (x, evalArg r a) | (x, a) <- fs ]
  New m        -> let md = evalMod r m in VInst md (instOf md)
  ProjU a l    -> vproj (eval r a) l
  Hole         -> VConst "_unfilled" []   -- reported by the filling pass

capp :: Clos -> Val -> Val
capp (Clos x b r) v = eval (EVar r x v) b

lcapp :: LClos -> Lvl -> Val
lcapp (LClos x b r) l = eval (ELvl r x l) b

-- Elimination.  A glued value keeps its name and extends its spine; its
-- unfolding is eliminated lazily.  A split whose argument is not yet a
-- constructor is stuck, and whnf resumes it: eval never forces a glued
-- value, which is what keeps it independent of the lock.
app :: Val -> Val -> Val
app (VLam f) v = capp f v
app (VDef i d sp u e) v = VDef i d (EApp v : sp) (app u v) e
app f@(VSplit _ _ bs r) v = case v of
  VCon c vs -> case lookup c bs of
    Just (xs, b) -> eval (bindAll r xs vs) b
    Nothing      -> error ("split: no branch for " ++ c)
  _ -> VApp f v
app u v = VApp u v

vfst :: Val -> Val
vfst (VPair u _)       = u
vfst (VDef i d sp u e) = VDef i d (EFst : sp) (vfst u) e
vfst w                 = VFst w

vsnd :: Val -> Val
vsnd (VPair _ v)       = v
vsnd (VDef i d sp u e) = VDef i d (ESnd : sp) (vsnd u) e
vsnd w                 = VSnd w

vproj :: Val -> Name -> Val
vproj (VStruct fs) l     = fromMaybe (error ("no field " ++ l)) (lookup l fs)
vproj (VInst _ r) l      = lookupVal r l
vproj (VNamedE _ _ v) l  = vproj v l
vproj (VDef i d sp u e) l = VDef i d (EProj l : sp) (vproj u l) e
vproj w l                = VProj w l

lapp :: Val -> Lvl -> Val
lapp (VLLam f) l        = lcapp f l
lapp (VDef i d sp u e) l = VDef i d (ELApp l : sp) (lapp u l) e
lapp w l                = VLApp w l

vidj :: Val -> Val -> Val -> Val -> Val -> Val -> Val
vidj _ _ _ d _ (VRefl _) = d
vidj a x c d y p         = VIdJ a x c d y p

bindAll :: Env -> [Name] -> [Val] -> Env
bindAll r []       []       = r
bindAll r (x : xs) (v : vs) = bindAll (EVar r x v) xs vs
bindAll _ _        _        = error "split: constructor arity mismatch"

-- a mutual group of definitions, modules and instances: each member is
-- evaluated ONCE (the lazy knot), and a definition is glued
mkGroup :: Env -> [Unit] -> Env
mkGroup r us = rho
 where
  ents = concatMap entry us
  rho = EDef r us ents (fragOf ents)
  entry u = case u of
    UDef i x _ b ds0 -> let (ds, encl) = splitDeps ds0
                        in [(x, EVal (VDef i (map (lookupDyn rho) ds) [] (eval rho b)
                                          [ (y, lookupDyn rho y) | y <- encl ]))]
    UMod i x mus ds -> [(x, EMod (Mod i (map (lookupDyn rho) ds) mus rho
                                   (if hasParams mus then Nothing
                                    else Just (instUnits rho mus []))))]
    UInst _ x m     -> [(x, EMod (evalMod rho m))]
    _               -> []

-- the dependencies of a definition, then (after "%encl") the parameters of
-- its enclosing segments
splitDeps :: [Name] -> ([Name], [Name])
splitDeps ds = case break (== "%encl") ds of
  (a, _ : b) -> (a, b)
  (a, [])    -> (a, [])

isGroupUnit :: Unit -> Bool
isGroupUnit u = case u of
  UDef{} -> True
  _      -> False

hasParams :: [Unit] -> Bool
hasParams = any isParam
 where isParam u = case u of { UPar{} -> True; ULvl _ -> True; _ -> False }

-- instantiate a module body: parameters bound to the arguments in order,
-- groups of definitions in between (they may mention earlier parameters,
-- and later parameter types may mention them)
instUnits :: Env -> [Unit] -> [Val] -> Env
instUnits r [] _ = r
instUnits r (u : us) vs = case (u, vs) of
  (UPar _ x _, v : vs')       -> instUnits (EVar r x v) us vs'
  (ULvl x, VLvl l : vs')      -> instUnits (ELvl r x l) us vs'
  (UPar _ x _, [])            -> error ("missing argument for " ++ x)
  (ULvl x, _)                 -> error ("missing level argument for " ++ x)
  (UMod{}, _)                 -> instUnits (mkGroup r [u]) us vs
  (UInst{}, _)                -> instUnits (mkGroup r [u]) us vs
  (UDef{}, _)                 -> let (g, rest) = span isGroupUnit (u : us)
                                 in instUnits (mkGroup r g) rest vs
  _                           -> instUnits r us vs

evalMod :: Env -> MExp -> Mod
evalMod r m = case m of
  MVar x    -> lookupMod r x
  MSub n x  -> lookupMod (instOf (evalMod r n)) x
  MApp n as -> let md = evalMod r n
               in md { modInst = Just (instUnits (modEnv md) (modUnits md) (map (evalArg r) as)) }

evalArg :: Env -> Arg -> Val
evalArg r (ATm e) = eval r e
evalArg r (ALv l) = VLvl (evalLv r l)

instOf :: Mod -> Env
instOf = fromMaybe (error "a module with parameters used without arguments") . modInst

lookupVal :: Env -> Name -> Val
lookupVal r0 x = go r0
 where
  go ENil = error ("unbound variable: " ++ x)
  go (EVar r y v) = if x == y then v else go r
  go (ELvl r y _) = if x == y then error ("level used as a term: " ++ x) else go r
  go (EDef r _ es _) = case lookup x es of
    Just (EVal v) -> v
    Just (EMod _) -> error ("module used as a term: " ++ x)
    Nothing       -> go r

lookupLvl :: Env -> Name -> Lvl
lookupLvl r0 x = go r0
 where
  go ENil = lvar x
  go (EVar r _ _) = go r
  go (ELvl r y l) = if x == y then l else go r
  go (EDef r _ _ _) = go r

lookupMod :: Env -> Name -> Mod
lookupMod r0 x = go r0
 where
  go ENil = error ("unbound module: " ++ x)
  go (EVar r _ _) = go r
  go (ELvl r _ _) = go r
  go (EDef r _ es _) = case lookup x es of
    Just (EMod m) -> m
    Just _        -> error ("not a module: " ++ x)
    Nothing       -> go r

-- the value of a dependency: a variable or a level
lookupDyn :: Env -> Name -> Val
lookupDyn r0 x = go r0
 where
  go ENil = VConst x []
  go (EVar r y v) = if x == y then v else go r
  go (ELvl r y l) = if x == y then VLvl l else go r
  go (EDef r _ _ _) = go r

-- the parameters of a segment, in order
paramNames :: [Unit] -> [Name]
paramNames us = [ x | u <- us, x <- case u of { UPar _ y _ -> [y]; ULvl y -> [y]; _ -> [] } ]

termParams :: [Unit] -> [Name]
termParams us = [ x | UPar _ x _ <- us ]

-- the unit declaring a member of a module body (not of its submodules)
memberUnit :: [Unit] -> Name -> Maybe Unit
memberUnit us x = case [ u | u <- us, unitName u == x ] of
  (u : _) -> Just u
  []      -> Nothing

------------------------------------------------------------------------
-- 4.  Weak head reduction under a lock strategy

-- Diagnostics (--unfolds): how often whnf unfolds each constant.  Off
-- unless the driver switches it on; the counter is global and only read by
-- the driver between declarations.
{-# NOINLINE unfoldOn #-}
unfoldOn :: IORef Bool
unfoldOn = unsafePerformIO (newIORef False)

{-# NOINLINE unfoldCount #-}
unfoldCount :: IORef (Map.Map Id Int)
unfoldCount = unsafePerformIO (newIORef Map.empty)

{-# NOINLINE countUnfold #-}
countUnfold :: Id -> a -> a
countUnfold i x = unsafePerformIO $ do
  on <- readIORef unfoldOn
  if on then modifyIORef' unfoldCount (Map.insertWith (+) i 1) else return ()
  return x

-- with SEG_DISTINCT set, the key includes a short print of the arguments
{-# NOINLINE distinctOn #-}
distinctOn :: IORef Bool
distinctOn = unsafePerformIO (newIORef False)

unfoldKey :: Id -> [Val] -> [Elim] -> Id
unfoldKey i d sp = unsafePerformIO $ do
  on <- readIORef distinctOn
  return (if on then i ++ " @ " ++ prettyAt 3 (rb False Set.empty 900 (VDef i d sp (VU lzero) [])) else i)

whnf :: Locks -> Val -> Val
whnf s v = case v of
  VDef i d sp u _ | Set.notMember i s -> countUnfold (unfoldKey i d sp) (whnf s u)
  VApp f a -> case whnf s f of
    f'@(VSplit{}) -> case whnf s a of
      a'@(VCon _ _) -> whnf s (app f' a')
      a'            -> VApp f' a'
    VLam cl -> whnf s (capp cl a)
    f' -> app f' a                       -- extend a locked constant's spine
  VFst p -> case whnf s p of
    VPair a _ -> whnf s a
    p'        -> vfst p'
  VSnd p -> case whnf s p of
    VPair _ b -> whnf s b
    p'        -> vsnd p'
  VProj p l -> case whnf s p of
    VStruct fs -> whnf s (fromMaybe (error ("no field " ++ l)) (lookup l fs))
    i@(VInst _ _) -> whnf s (vproj i l)
    VNamedE _ _ v -> whnf s (vproj v l)
    p'         -> vproj p' l
  VLApp t l -> case whnf s t of
    VLLam cl -> whnf s (lcapp cl l)
    t'       -> VLApp t' l
  VIdJ a x c d y p -> case whnf s p of
    VRefl _ -> whnf s d
    p'      -> VIdJ a x c d y p'
  _ -> v

------------------------------------------------------------------------
-- 5.  Conversion
--
-- Names first: two glued values with the same head and equal dynamic parts
-- and spines are equal without unfolding.  Otherwise both sides are put in
-- weak head normal form under the strategy (a locked head stays) and
-- compared structurally.  Locking only under-approximates conversion.

data CC = CC { ccK :: Int, ccTh :: Theory, ccS :: Locks }

conv :: CC -> Val -> Val -> Bool
conv c u v
  | thLoop (ccTh c) = True
  | eqVal u v       = True                  -- cubicaltt:  conv ns u v | u == v
  | sameDef u v     = True                  -- lazy delta: the same constant at convertible arguments
  | otherwise       = traceConv u v (conv' c (whnf (ccS c) u) (whnf (ccS c) v))
 where
  -- two applications of the same defined constant are equal when their
  -- arguments are (their unfoldings are then equal); otherwise unfold
  sameDef (VDef i1 d1 s1 _ _) (VDef i2 d2 s2 _ _) =
    i1 == i2 && length s1 == length s2 && convs c d1 d2 && convSp c s1 s2
  sameDef _ _ = False

-- Structural equality of values (cubicaltt's derived Eq on Val): no
-- reduction, no unfolding.  A glued constant is its name and arguments
-- (equal names and arguments have equal unfoldings, so the unfolding is not
-- compared); a closure is its binder, its body and its environment; a
-- block of definitions in an environment is the ids of its units.
{-# NOINLINE traceOn #-}
traceOn :: Bool
traceOn = unsafePerformIO (fmap (/= Nothing) (lookupEnv "SEG_TRACE"))

{-# NOINLINE traceSub #-}
traceSub :: Val -> Val -> a -> a
traceSub u v x = unsafePerformIO (do
  putStrLn ("SUB   " ++ prettyAt 6 (rb False Set.empty 900 u) ++ "\n  <=? " ++ prettyAt 6 (rb False Set.empty 900 v))
  return x)

{-# NOINLINE traceConv #-}
traceConv :: Val -> Val -> a -> a
traceConv u v x
  | traceOn = unsafePerformIO (do
      putStrLn ("CONV  " ++ prettyAt 5 (rb False Set.empty 900 u) ++ "\n   =? " ++ prettyAt 5 (rb False Set.empty 900 v))
      return x)
  | otherwise = x

eqVal :: Val -> Val -> Bool
eqVal u v = case (u, v) of
  (VU l, VU m)                     -> l == m
  (VGen i, VGen j)                 -> i == j
  (VLvl l, VLvl m)                 -> l == m
  (VConst i d, VConst j e)         -> i == j && eqVals d e
  (VDef i d s _ _, VDef j e t _ _) -> i == j && eqVals d e && eqSp s t
  (VApp a b, VApp a' b')           -> eqVal a a' && eqVal b b'
  (VLam f, VLam g)                 -> eqClos f g
  (VPi a f, VPi b g)               -> eqVal a b && eqClos f g
  (VSig (Just (i, _, d)) _ _, VSig (Just (j, _, e)) _ _) -> i == j && eqVals d e
  (VSig _ a f, VSig _ b g)         -> eqVal a b && eqClos f g
  (VRec (Just (i, _, d)) _ _, VRec (Just (j, _, e)) _ _) -> i == j && eqVals d e
  (VCon c as, VCon d bs)           -> c == d && eqVals as bs
  (VSum t d _ _, VSum t' d' _ _)   -> t == t' && eqVals d d'
  (VSplit t d _ _, VSplit t' d' _ _) -> t == t' && eqVals d d'
  (VPair a b, VPair a' b')         -> eqVal a a' && eqVal b b'
  (VFst a, VFst b)                 -> eqVal a b
  (VSnd a, VSnd b)                 -> eqVal a b
  (VRec _ t r, VRec _ t' r')       -> t == t' && eqEnv r r'
  (VStruct fs, VStruct gs)         -> map fst fs == map fst gs && eqVals (map snd fs) (map snd gs)
  (VProj a l, VProj b m)           -> l == m && eqVal a b
  (VId a x y, VId b x' y')         -> eqVal a b && eqVal x x' && eqVal y y'
  (VRefl a, VRefl b)               -> eqVal a b
  (VIdJ a b c d e f, VIdJ a' b' c' d' e' f') -> eqVals [a,b,c,d,e,f] [a',b',c',d',e',f']
  (VLPi f, VLPi g)                 -> eqLClos f g
  (VLLam f, VLLam g)               -> eqLClos f g
  (VLApp a l, VLApp b m)           -> l == m && eqVal a b
  (VCPi cs a, VCPi ds b)           -> cs == ds && eqVal a b
  (VSegT m fs, VSegT n gs)         -> modId m == modId n && eqVals (modDyn m) (modDyn n)
                                      && map fst fs == map fst gs && eqVals (map snd fs) (map snd gs)
  (VNamedE i d _, VNamedE j e _) | i == j -> eqVals d e
  (VNamedE _ _ a, b)               -> eqVal a b
  (a, VNamedE _ _ b)               -> eqVal a b
  (VInst m r, VInst n r')          -> modId m == modId n
                                      && and [ eqVal (lookupDyn r x) (lookupDyn r' x) | x <- paramNames (modUnits m) ]
  _                                -> False

eqVals :: [Val] -> [Val] -> Bool
eqVals as bs = length as == length bs && and (zipWith eqVal as bs)

eqSp :: [Elim] -> [Elim] -> Bool
eqSp s t = length s == length t && and (zipWith e s t)
 where e x y = case (x, y) of
         (EApp a, EApp b)    -> eqVal a b
         (EFst, EFst)        -> True
         (ESnd, ESnd)        -> True
         (EProj l, EProj m)  -> l == m
         (ELApp l, ELApp m)  -> l == m
         _                   -> False

eqClos :: Clos -> Clos -> Bool
eqClos (Clos x e r) (Clos y e' r') = x == y && e == e' && eqEnv r r'

eqLClos :: LClos -> LClos -> Bool
eqLClos (LClos x e r) (LClos y e' r') = x == y && e == e' && eqEnv r r'

-- Two environments of the same expression are equal when their VARIABLES
-- (term and level) have equal values.  The definition groups are static:
-- the same expression sees the same groups, and their values depend only
-- on the variables below them, so they are skipped, not compared.
eqEnv :: Env -> Env -> Bool
eqEnv r s = case (skipDefs r, skipDefs s) of
  (ENil, ENil)               -> True
  (EVar r1 x v, EVar s1 y w) -> x == y && eqVal v w && eqEnv r1 s1
  (ELvl r1 x l, ELvl s1 y m) -> x == y && l == m && eqEnv r1 s1
  _                          -> False

skipDefs :: Env -> Env
skipDefs r = case r of
  EDef r1 _ _ _ -> skipDefs r1
  _             -> r

conv' :: CC -> Val -> Val -> Bool
conv' c u1 u2 = case (u1, u2) of
  (VDef i1 d1 s1 _ _, VDef i2 d2 s2 _ _) -> i1 == i2 && convs c d1 d2 && convSp c s1 s2
  (VU l, VU m)                 -> eqLvl th l m
  (VLvl l, VLvl m)             -> eqLvl th l m
  (VGen i, VGen j)             -> i == j
  (VConst i d1, VConst j d2)   -> i == j && convs c d1 d2
  (VLam _, _)                  -> etaEq
  (_, VLam _)                  -> etaEq
  (VLLam _, _)                 -> letaEq
  (_, VLLam _)                 -> letaEq
  (VPair a b, VPair a' b')     -> conv c a a' && conv c b b'
  (VPair a b, w)               -> conv c a (vfst w) && conv c b (vsnd w)
  (w, VPair a b)               -> conv c (vfst w) a && conv c (vsnd w) b
  -- two elements written as  new M[..] / struct {..}: ONLY the dynamic
  -- part is compared (same occurrence, convertible values), never the
  -- static part (the fields)
  -- different occurrences: different names, not equal (Half, Gofer)
  (VNamedE i d1 _, VNamedE j d2 _) -> i == j && convs c d1 d2
  (VNamedE _ _ a, w)           -> conv c a w
  (w, VNamedE _ _ a)           -> conv c w a
  (VInst m1 r1, VInst m2 r2)   -> modId m1 == modId m2
                                  && and [ conv c (lookupDyn r1 x) (lookupDyn r2 x) | x <- paramNames (modUnits m1) ]
  (VInst m r, w)               -> and [ conv c (lookupDyn r x) (vproj w x) | x <- termParams (modUnits m) ]
  (w, VInst m r)               -> and [ conv c (vproj w x) (lookupDyn r x) | x <- termParams (modUnits m) ]
  (VSegT m1 f1, VSegT m2 f2)   -> modId m1 == modId m2 && convs c (modDyn m1) (modDyn m2)
                                  && map fst f1 == map fst f2
                                  && convs c (map snd f1) (map snd f2)
  (VStruct fs, VStruct gs)     -> map fst fs == map fst gs
                                  && and (zipWith (conv c) (map snd fs) (map snd gs))
  (VStruct fs, w)              -> and [ conv c a (vproj w l) | (l, a) <- fs ]
  (w, VStruct fs)              -> and [ conv c (vproj w l) a | (l, a) <- fs ]
  (VPi a f, VPi b g)           -> conv c a b && conv c' (capp f x) (capp g x)
  -- by name: the same occurrence and the same values of its dependencies
  (VSig (Just (i, _, d1)) _ _, VSig (Just (j, _, d2)) _ _) -> i == j && convs c d1 d2
  (VRec (Just (i, _, d1)) _ _, VRec (Just (j, _, d2)) _ _) -> i == j && convs c d1 d2
  -- an unnamed one (the inner part of a Sigma chain): structurally
  (VSig _ a f, VSig _ b g)     -> conv c a b && conv c' (capp f x) (capp g x)
  (VRec _ t1 r1, VRec _ t2 r2) -> convTel c t1 r1 t2 r2
  (VLPi f, VLPi g)             -> conv cl (lcapp f lx) (lcapp g lx)
  (VCPi cs a, VCPi ds b)       -> equivCs th cs ds && conv (withCs cs) a b
  (VCPi cs a, w)               -> all (validCstr th) cs && conv c a w
  (w, VCPi cs a)               -> all (validCstr th) cs && conv c w a
  (VId a x1 y1, VId b x2 y2)   -> conv c a b && conv c x1 x2 && conv c y1 y2
  (VRefl a, VRefl b)           -> conv c a b
  (VIdJ a1 b1 c1 d1 e1 f1, VIdJ a2 b2 c2 d2 e2 f2) ->
    convs c [a1,b1,c1,d1,e1,f1] [a2,b2,c2,d2,e2,f2]
  (VCon k1 vs, VCon k2 ws)     -> k1 == k2 && convs c vs ws
  (VSum t1 d1 _ _, VSum t2 d2 _ _)       -> t1 == t2 && convs c d1 d2
  (VSplit t1 d1 _ _, VSplit t2 d2 _ _)   -> t1 == t2 && convs c d1 d2
  (VApp a b, VApp a' b')       -> conv c a a' && conv c b b'
  (VFst a, VFst b)             -> conv c a b
  (VSnd a, VSnd b)             -> conv c a b
  (VProj a l, VProj b l')      -> l == l' && conv c a b
  (VLApp a l, VLApp b m)       -> conv c a b && eqLvl th l m
  _                            -> False
 where
  th  = ccTh c
  k   = ccK c
  x   = VGen k
  c'  = c { ccK = k + 1 }
  lxn = "%" ++ show k
  lx  = lvar lxn
  cl  = c { ccK = k + 1, ccTh = addVar lxn th }
  etaEq  = conv c' (app u1 x) (app u2 x)
  letaEq = conv cl (lapp u1 lx) (lapp u2 lx)
  withCs cs = c { ccTh = foldr addCstr th cs }

equivCs :: Theory -> [Cstr] -> [Cstr] -> Bool
equivCs th cs ds = all (validCstr (foldr addCstr th ds)) cs
                && all (validCstr (foldr addCstr th cs)) ds

convs :: CC -> [Val] -> [Val] -> Bool
convs _ []       []       = True
convs c (u : us) (v : vs) = conv c u v && convs c us vs
convs _ _        _        = False

convSp :: CC -> [Elim] -> [Elim] -> Bool
convSp _ [] [] = True
convSp c (e1 : s1) (e2 : s2) = ok && convSp c s1 s2
 where
  ok = case (e1, e2) of
    (EApp a, EApp b)     -> conv c a b
    (EFst, EFst)         -> True
    (ESnd, ESnd)         -> True
    (EProj l, EProj l')  -> l == l'
    (ELApp l, ELApp m)   -> eqLvl (ccTh c) l m
    _                    -> False
convSp _ _ _ = False

convTel :: CC -> Tel -> Env -> Tel -> Env -> Bool
convTel _ [] _ [] _ = True
convTel c ((l1, a1) : t1) r1 ((l2, a2) : t2) r2 =
  l1 == l2 && conv c (eval r1 a1) (eval r2 a2)
  && convTel c { ccK = ccK c + 1 } t1 (EVar r1 l1 x) t2 (EVar r2 l2 x)
 where x = VGen (ccK c)
convTel _ _ _ _ _ = False

------------------------------------------------------------------------
-- 6.  Read-back.  rb keeps glued values as their names (diagnostics);
-- nf unfolds everything the strategy allows (#normal).

rb :: Bool -> Locks -> Int -> Val -> Exp
rb full s k v0 = case (if full then whnf s v0 else v0) of
  VU l          -> U (lvToLv l)
  VLvl l        -> Var (showLvl l)
  VGen i        -> Var ("#" ++ show i)
  VConst i d    -> Var (shortId i ++ dynS d)
  VDef i d sp _ _ -> foldr elimE (Var (shortId i ++ dynS d)) sp
  VApp a b      -> App (go a) (go b)
  VLam f        -> Lam (nm k) (rb full s (k+1) (capp f (VGen k)))
  VPi a f       -> Pi (nm k) (go a) (rb full s (k+1) (capp f (VGen k)))
  VCon c vs     -> Con c (map go vs)
  VSum t _ _ _  -> Var (shortId t)
  VSplit t _ _ _ -> Var (shortId t)
  VSig _ a f    -> Sig (nm k) (go a) (rb full s (k+1) (capp f (VGen k)))
  VPair a b     -> Pair (go a) (go b)
  VFst a        -> Fst (go a)
  VSnd a        -> Snd (go a)
  VRec _ tel r  -> Rec (rbTel k tel r)
  VStruct fs    -> Struct [ (l, go a) | (l, a) <- fs ]
  VNamedE _ _ a -> go a
  VProj a l     -> Proj (go a) l
  VId a x y     -> Id (go a) (go x) (go y)
  VRefl a       -> Refl (go a)
  VIdJ a b c d e f -> IdJ (go a) (go b) (go c) (go d) (go e) (go f)
  VLPi f        -> LPi (lnm k) (rb full s (k+1) (lcapp f (lvar (lnm k))))
  VLLam f       -> LLam (lnm k) (rb full s (k+1) (lcapp f (lvar (lnm k))))
  VLApp a l     -> LApp (go a) (lvToLv l)
  VCPi cs a     -> CPi (map csToCs cs) (go a)
  VSegT m fs    -> SegT (MVar (shortId (modId m))) [ (x, rbArg a) | (x, a) <- fs ]
  VInst m r     -> New (MApp (MVar (shortId (modId m)))
                          [ rbArg (lookupDyn r x) | x <- paramNames (modUnits m) ])
 where
  rbArg (VLvl l) = ALv (lvToLv l)
  rbArg a        = ATm (go a)
  go = rb full s k
  nm i  = "#" ++ show i
  lnm i = "%" ++ show i
  elimE el h = case el of
    EApp a  -> App h (go a)
    EFst    -> Fst h
    ESnd    -> Snd h
    EProj l -> Proj h l
    ELApp l -> LApp h (lvToLv l)
  -- the dynamic part, when there is one:  M.f{A := N, ..}
  dynS [] = ""
  dynS d  = "{" ++ commaSep (map (prettyAt 3 . go) d) ++ "}"
  rbTel _ [] _ = []
  rbTel j ((l, a) : tel) r = (l, rb full s j (eval r a)) : rbTel (j+1) tel (EVar r l (VGen j))

lvToLv :: Lvl -> Lv
lvToLv l = foldr1 LMax [ iterate LSuc (if x == "0" then LZero else LV x) !! n | (x, n) <- latoms l ]

csToCs :: Cstr -> Cs
csToCs c = case c of
  CEq l m -> Cs (lvToLv l) REq (lvToLv m)
  CLe l m -> Cs (lvToLv l) RLe (lvToLv m)
  CLt l m -> Cs (lvToLv l) RLt (lvToLv m)

-- the printed name: drop the occurrence tag
shortId :: Id -> String
shortId = takeWhile (/= '#')

------------------------------------------------------------------------
-- 7.  Printing

pretty :: Exp -> String
pretty = prettyAt 8

prettyAt :: Int -> Exp -> String
prettyAt lim = pr 0 lim
 where
  pr :: Int -> Int -> Exp -> String
  go :: Int -> Int -> Exp -> String
  pr _ 0 _ = ".."
  pr d n e0 = go d n e0
  go _ _ (U l)       = "U " ++ plv True l
  go _ _ (Var x)     = x
  go _ _ (Sum t _ _) = shortId t
  go _ _ (Split t _ _) = shortId t
  go d n (App a b)   = paren (d > 10) (pr 10 n a ++ " " ++ pr 11 (n-1) b)
  go d n (LApp a l)  = paren (d > 10) (pr 10 n a ++ " @" ++ plv True l)
  go d n (Lam x b)   = paren (d > 0) ("\\ " ++ x ++ " -> " ++ pr 0 (n-1) b)
  go d n (LLam x b)  = paren (d > 0) ("<" ++ x ++ "> " ++ pr 0 (n-1) b)
  go d n (LPi x b)   = paren (d > 1) ("[" ++ x ++ "] " ++ pr 1 (n-1) b)
  go d n (CPi cs b)  = paren (d > 1) ("[" ++ commaSep (map pcs cs) ++ "] " ++ pr 1 (n-1) b)
  go d n (Pi x a b)
    | x == "_"       = paren (d > 1) (pr 2 (n-1) a ++ " -> " ++ pr 1 (n-1) b)
    | otherwise      = paren (d > 1) ("(" ++ x ++ " : " ++ pr 0 (n-1) a ++ ") -> " ++ pr 1 (n-1) b)
  go d n (Sig x a b)
    | x == "_"       = paren (d > 2) (pr 3 (n-1) a ++ " * " ++ pr 2 (n-1) b)
    | otherwise      = paren (d > 2) ("(" ++ x ++ " : " ++ pr 0 (n-1) a ++ ") * " ++ pr 2 (n-1) b)
  go _ n (Pair a b)  = "(" ++ pr 0 (n-1) a ++ ", " ++ pr 0 (n-1) b ++ ")"
  go d n (Fst a)     = paren (d > 11) (pr 11 (n-1) a ++ ".1")
  go d n (Snd a)     = paren (d > 11) (pr 11 (n-1) a ++ ".2")
  go d n (Proj a l)  = paren (d > 11) (pr 11 (n-1) a ++ "." ++ l)
  go _ n (Rec tel)   = "sig { " ++ semiSep [ l ++ " : " ++ pr 0 (n-1) a | (l, a) <- tel ] ++ " }"
  go _ n (Struct fs) = "struct { " ++ semiSep [ l ++ " = " ++ pr 0 (n-1) a | (l, a) <- fs ] ++ " }"
  go d n (Con c as)
    | null as        = c
    | otherwise      = paren (d > 10) (c ++ concatMap ((' ' :) . pr 11 (n-1)) as)
  go d n (Id a x y)  = paren (d > 10) ("Id " ++ unwords (map (pr 11 (n-1)) [a, x, y]))
  go d n (Refl a)    = paren (d > 10) ("refl " ++ pr 11 (n-1) a)
  go d n (IdJ a x c e y q) = paren (d > 10) ("idJ " ++ unwords (map (pr 11 (n-1)) [a,x,c,e,y,q]))
  go d n (Let _ b)   = paren (d > 0) ("let {..} in " ++ pr 0 (n-1) b)
  go _ _ (Acc m x)   = case pm m of { "" -> x; p -> p ++ "." ++ x }
  go _ _ (SegT m [])  = pm m
  go _ _ (SegT m fs)  = pm m ++ "[" ++ commaSep [ x ++ " := " ++ parg a | (x, a) <- fs ] ++ "]"
  go d _ (New m)      = paren (d > 10) ("new " ++ pm m)
  go _ _ Hole         = "_"
  go d n (Named _ _ a) = pr d n a
  go d n (ProjU a l)  = paren (d > 11) (pr 11 (n-1) a ++ "." ++ l)
  paren True  t = "(" ++ t ++ ")"
  paren False t = t
  pm (MVar x)     = if take 5 x == "open#" then "" else x
  pm (MSub m x)   = pm m ++ "." ++ x
  pm (MApp m as)  = pm m ++ "[" ++ commaSep (map parg as) ++ "]"
  parg (ATm e) = pr 0 3 e
  parg (ALv l) = plv False l
  pcs (Cs l r m) = plv False l ++ (case r of REq -> " = "; RLe -> " <= "; RLt -> " < ") ++ plv False m

plv :: Bool -> Lv -> String
plv atomic l = case l of
  LV x     -> x
  LZero    -> "0"
  LSuc m   -> plv True m ++ "+"
  LMax a b -> (if atomic then \t -> "(" ++ t ++ ")" else id) (plv False a ++ " \\/ " ++ plv False b)

commaSep :: [String] -> String
commaSep [] = ""
commaSep xs = foldr1 (\a b -> a ++ ", " ++ b) xs

semiSep :: [String] -> String
semiSep [] = ""
semiSep xs = foldr1 (\a b -> a ++ " ; " ++ b) xs

------------------------------------------------------------------------
-- 8.  The checking context: the units seen so far

data Cx = Cx
  { cxK     :: Int
  , cxEnv   :: Env
  , cxTys   :: [(Name, Val)]
  , cxTh    :: Theory
  , cxLocks :: Locks
  , cxLvls  :: [Name]                -- the level variables in scope
  , cxPSorts :: [(Name, Res Lvl)]    -- sorts of the parameters of this body
  , cxSegSort :: [(Id, [(Name, Res Lvl)])]  -- per segment, its parameters' sorts
  }

emptyCx :: Cx
emptyCx = Cx 0 ENil [] emptyTheory Set.empty [] [] []

cc :: Cx -> CC
cc cx = CC (cxK cx) (cxTh cx) (cxLocks cx)

force :: Cx -> Val -> Val
force cx = whnf (cxLocks cx)

ev :: Cx -> Exp -> Val
ev cx = eval (cxEnv cx)

-- extend by a variable of type t, bound to a fresh generic
extVar :: Cx -> Name -> Val -> (Cx, Val)
extVar cx x t = (cx { cxK = k + 1, cxEnv = EVar (cxEnv cx) x v, cxTys = (x, t) : cxTys cx }, v)
 where k = cxK cx
       v = etaV t (VGen k)

-- A variable of segment type is bound to its eta-expansion: an instance
-- whose fields are its projections, or the fixed values for the fields
-- the type implements.  So  c : M[x := e]  gives  c.x = e  on the nose,
-- and the defined members of M are evaluated in c's instance.
etaV :: Val -> Val -> Val
etaV t v = case whnf Set.empty t of
  VSegT md fs
    | all (`elem` map fst fs) [ y | ULvl y <- modUnits md ] ->
        VInst md (instUnits (modEnv md) (modUnits md)
                    [ fromMaybe (vproj v p) (lookup p fs) | p <- paramNames (modUnits md) ])
  _ -> v

-- extend by a level variable, bound to a fresh generic level
extLvl :: Cx -> Name -> (Cx, Lvl)
extLvl cx x = ( cx { cxK = k + 1, cxEnv = ELvl (cxEnv cx) x l
                   , cxTh = addVar g (cxTh cx), cxLvls = x : cxLvls cx }
              , l )
 where k = cxK cx
       g = "%" ++ show k
       l = lvar g

addCs :: Cx -> [Cstr] -> Cx
addCs cx cs = cx { cxTh = foldr addCstr (cxTh cx) cs }

showV :: Cx -> Val -> String
showV cx v = prettyAt 16 (rb False (cxLocks cx) (cxK cx) v)

type Res a = Either String a

ok :: Res ()
ok = Right ()

failWith :: String -> Res a
failWith = Left

------------------------------------------------------------------------
-- 9.  Type checking

checkLv :: Cx -> Lv -> Res ()
checkLv cx l = case l of
  LV x | x `elem` cxLvls cx -> ok
       | otherwise          -> failWith ("unknown level variable " ++ x)
  LSuc m   -> checkLv cx m
  LMax a b -> checkLv cx a >> checkLv cx b
  LZero    -> ok

checkCs :: Cx -> Cs -> Res Cstr
checkCs cx c@(Cs l _ m) = do checkLv cx l; checkLv cx m; Right (evalCs (cxEnv cx) c)

-- A is a type: small (A : U l) or large ([a]B, [psi]B, Pi with a large part)
checkType :: Cx -> Exp -> Res ()
checkType cx e = case e of
  Pi x a b -> do checkType cx a
                 checkType (fst (extVar cx x (ev cx a))) b
  Sig x a b -> do checkType cx a
                  checkType (fst (extVar cx x (ev cx a))) b
  LPi a b  -> checkType (fst (extLvl cx a)) b
  CPi cs b -> do vs <- mapM (checkCs cx) cs
                 checkType (addCs cx vs) b
  SegT m fs -> do _ <- checkSegT cx m fs; ok
  Named _ _ e' -> checkType cx e'
  Let us b -> do cx' <- checkLocal cx us
                 checkType cx' b
  _ -> do t <- inferD cx e
          case force cx t of
            VU _ -> ok
            t'   -> failWith ("not a type: " ++ pretty e ++ "\n  it has type " ++ showV cx t')

-- the level of a small type
inferSort :: Cx -> Exp -> Res Lvl
inferSort cx e = do
  t <- inferD cx e
  case force cx t of
    VU l -> Right l
    t'   -> failWith ("not a small type: " ++ pretty e ++ "\n  it has type " ++ showV cx t')

-- cumulativity, at the top only (bcde.pdf App. B; BCDE4's SubTy)
sub :: Cx -> Val -> Val -> Bool
sub cx t' t = (if traceOn then traceSub t' t else id) $ case (force cx t', force cx t) of
  (VU l, VU m) -> leq (cxTh cx) l m
  -- an extension with more fields fixed is a subtype (Arend)
  (VSegT m1 f1, VSegT m2 f2) ->
    modId m1 == modId m2 && convs (cc cx) (modDyn m1) (modDyn m2)
    && and [ maybe False (\v' -> conv (cc cx) v' v) (lookup x f1) | (x, v) <- f2 ]
  _            -> conv (cc cx) t' t

check :: Cx -> Exp -> Val -> Res ()
check cx e t0 = case (e, t) of
  (_, VCPi cs a) -> check (addCs cx cs) e a          -- <psi> t, silently
  (Lam x b, VPi a f) -> let (cx', v) = extVar cx x a in check cx' b (capp f v)
  (LLam x b, VLPi f) -> let (cx', l) = extLvl cx x in check cx' b (lcapp f l)
  (Pi x a b, VU _) -> do check cx a t
                         check (fst (extVar cx x (ev cx a))) b t
  (Sig x a b, VU _) -> do check cx a t
                          check (fst (extVar cx x (ev cx a))) b t
  (Rec tel, VU _) -> checkTelIn cx tel t
  (Pair a b, VSig _ ta f) -> do check cx a ta
                                check cx b (capp f (ev cx a))
  (Struct fs, VRec _ tel r) -> checkStruct cx fs tel r
  (Refl a, VId ta x y) -> do
    check cx a ta
    let va = ev cx a
    if conv (cc cx) va x && conv (cc cx) va y then ok
      else failWith ("refl " ++ pretty a ++ " does not prove " ++ showV cx t)
  (Sum _ _ cs, VU _) -> mapM_ (\(_, tel) -> checkTelIn cx tel t) cs
  (Con c as, VSum _ _ cs r) -> case lookup c cs of
    Nothing  -> failWith ("constructor " ++ c ++ " is not in " ++ showV cx t)
    Just tel -> checkArgs cx as tel r
  (Split _ _ bs, VPi dom f) -> case force cx dom of
    VSum _ _ cs r -> checkSplit cx bs cs r f
    d -> failWith ("split on a non-sum type " ++ showV cx d)
  (Named _ _ e', _) -> check cx e' t0
  (Let us b, _) -> do cx' <- checkLocal cx us
                      check cx' b t
  _ -> do
    t' <- inferD cx e
    if sub cx t' t || subSeg t' then ok
      else failWith ("type mismatch for  " ++ pretty e ++
                     "\n  expected : " ++ showV cx t ++
                     "\n  inferred : " ++ showV cx t')
 where
  t = force cx t0
  -- a fixed field of the expected segment type may be known from the
  -- element itself rather than from its type: compare it with the value
  subSeg t' = case (force cx t', t) of
    (VSegT m1 f1, VSegT m2 f2) ->
      modId m1 == modId m2 && convs (cc cx) (modDyn m1) (modDyn m2)
      && and [ maybe (conv (cc cx) (vproj (ev cx e) x) v) (\v' -> conv (cc cx) v' v) (lookup x f1)
             | (x, v) <- f2 ]
    _ -> False

-- discharge constraint products: t : [psi]A  is  t : A  once psi is valid
inferD :: Cx -> Exp -> Res Val
inferD cx e = do
  t <- infer cx e
  discharge t
 where
  discharge t = case force cx t of
    VCPi cs a
      | all (validCstr (cxTh cx)) cs -> discharge a
      | otherwise -> failWith ("constraint not valid here: " ++ showV cx (VCPi cs a)
                               ++ "\n  for " ++ pretty e)
    _ -> Right t                     -- unforced: names survive (for quoting)

infer :: Cx -> Exp -> Res Val
infer cx e = case e of
  U l -> do checkLv cx l; Right (VU (lsuc (evalLv (cxEnv cx) l)))
  Var x -> case lookup x (cxTys cx) of
    Just t  -> Right t
    Nothing -> failWith ("no type for " ++ x)
  App f a -> do
    tf <- inferD cx f
    case force cx tf of
      VPi ta cl -> do check cx a ta
                      Right (capp cl (ev cx a))
      t' -> failWith ("not a function: " ++ pretty f ++ "\n  it has type " ++ showV cx t')
  LApp f l -> do
    checkLv cx l
    tf <- inferD cx f
    case force cx tf of
      VLPi cl -> Right (lcapp cl (evalLv (cxEnv cx) l))
      t' -> failWith ("not level-polymorphic: " ++ pretty f ++ "\n  it has type " ++ showV cx t')
  Pi x a b -> do la <- inferSort cx a
                 lb <- inferSort (fst (extVar cx x (ev cx a))) b
                 Right (VU (lmax la lb))
  Sig x a b -> do la <- inferSort cx a
                  lb <- inferSort (fst (extVar cx x (ev cx a))) b
                  Right (VU (lmax la lb))
  Rec tel -> do ls <- inferTel cx tel
                Right (VU (foldr lmax lzero ls))
  Id a x y -> do
    l <- inferSort cx a
    let va = ev cx a
    check cx x va
    check cx y va
    Right (VU l)
  Refl a -> do
    ta <- inferD cx a
    let va = ev cx a
    Right (VId ta va va)
  IdJ a x c d y p -> do
    _ <- inferSort cx a
    let va = ev cx a
        vx = ev cx x
    check cx x va
    checkMotive cx c va vx
    let vc = ev cx c
    check cx d (app (app vc vx) (VRefl vx))
    check cx y va
    check cx p (VId va vx (ev cx y))
    Right (app (app vc (ev cx y)) (ev cx p))
  Fst a -> do
    t <- inferD cx a
    case force cx t of
      VSig _ ta _ -> Right ta
      t' -> failWith ("not a pair: " ++ pretty a ++ " : " ++ showV cx t')
  Snd a -> do
    t <- inferD cx a
    case force cx t of
      VSig _ _ cl -> Right (capp cl (vfst (ev cx a)))
      t' -> failWith ("not a pair: " ++ pretty a ++ " : " ++ showV cx t')
  Proj a l -> do
    t <- inferD cx a
    case force cx t of
      VRec _ tel r -> fieldType cx (ev cx a) tel r l
      VSegT md fs -> do
        let v = ev cx a
            r = case v of
              VInst _ r' -> r'
              VNamedE _ _ (VInst _ r') -> r'
              _ -> instUnits (modEnv md) (modUnits md)
                     [ fromMaybe (vproj v p) (lookup p fs) | p <- paramNames (modUnits md) ]
        case memberUnit (modUnits md) l of
          Just (UDef _ _ ty _ _) -> Right (eval r ty)
          Just (UPar _ _ ty)     -> Right (eval r ty)
          _ -> failWith ("no member " ++ l ++ " in " ++ showV cx t)
      t' -> failWith ("not a record: " ++ pretty a ++ " : " ++ showV cx t')
  Named _ _ e' -> infer cx e'
  Let us b -> do
    cx' <- checkLocal cx us
    infer cx' b
  SegT m fs -> do
    (md, vs) <- checkSegT cx m fs
    -- the universe of the Sigma of the fields NOT fixed (Arend)
    case lookup (modId md) (cxSegSort cx) of
      Nothing -> failWith ("no sort known for the segment " ++ showM m)
      Just ps -> case sequence [ r | (x, r) <- ps, x `notElem` map fst vs ] of
        Right ls -> Right (VU (lsubst (segLvl md vs) (foldr lmax lzero ls)))
        Left _   -> failWith ("the segment " ++ showM m ++ " has a large free parameter: it is not in a universe")
  New m -> do
    md <- checkMod cx m
    -- the type fixes the levels only: a fixed field is read off the
    -- element's value where needed (subSeg), and a type that does not
    -- mention the fields can be a codomain (apH (\ c -> new M[.., c]))
    let r = instOf md
    Right (VSegT md [ (p, VLvl l) | ULvl p <- modUnits md, VLvl l <- [lookupDyn r p] ])
  Acc m x -> do
    md <- checkMod cx m
    case memberUnit (modUnits md) x of
      Just (UDef _ _ a _ _) -> Right (eval (instOf md) a)
      Just (UPar _ _ a)     -> Right (eval (instOf md) a)
      _ -> failWith ("no member " ++ x ++ " in the module")
  _ -> failWith ("cannot infer a type for  " ++ pretty e)

-- a segment type  M[x := e, ..] : the fixed fields are checked against the
-- parameters in order; every level parameter must be fixed (levels are
-- not fields); the constraints of M must hold for them.
checkSegT :: Cx -> MExp -> [(Name, Arg)] -> Res (Mod, [(Name, Val)])
checkSegT cx m fs = do
  md <- checkModHead cx m
  let ps = paramNames (modUnits md)
  case [ x | (x, _) <- fs, x `notElem` ps ] of
    (x : _) -> failWith ("the segment " ++ showM m ++ " has no parameter " ++ x)
    [] -> ok
  vs <- go (modEnv md) (modUnits md)
  Right (md, vs)
 where
  go _ [] = Right []
  go r (u : us) = case u of
    UPar i x a -> case lookup x fs of
      Just (ATm e) -> do
        inCtx ("in the field " ++ x) (check cx e (eval r a))
        let v = ev cx e
        vs <- go (EVar r x v) us
        Right ((x, v) : vs)
      Just (ALv _) -> failWith ("the field " ++ x ++ " is not a level")
      Nothing -> go (EVar r x (VConst ("?" ++ i) [])) us
    ULvl x -> case lookup x fs of
      Just (ALv l) -> do
        checkLv cx l
        let v = evalLv (cxEnv cx) l
        vs <- go (ELvl r x v) us
        Right ((x, VLvl v) : vs)
      _ -> failWith ("the level parameter " ++ x ++ " of " ++ showM m ++ " must be given")
    UCstr cs ->
      let vs = map (evalCs r) cs
      in if all (validCstr (cxTh cx)) vs then go r us
         else failWith ("the levels do not satisfy the constraint "
                        ++ commaSep [ prettyCs (csToCs c) | c <- vs ])
    UDef{} -> let (g, rest) = span isGroupUnit (u : us) in go (mkGroup r g) rest
    UMod{} -> go (mkGroup r [u]) us
    UInst{} -> go (mkGroup r [u]) us
    _ -> go r us

-- the level of a segment's universe at the given levels
segLvl :: Mod -> [(Name, Val)] -> LName -> Lvl
segLvl md vs x = case lookup x vs of
  Just (VLvl l) -> l
  _             -> lookupLvl (modEnv md) x

-- the motive of J:  (z : A) -> Id A a z -> type
checkMotive :: Cx -> Exp -> Val -> Val -> Res ()
checkMotive cx c va vx = case c of
  Lam z (Lam q body) -> do
    let (cx1, vz) = extVar cx z va
        (cx2, _)  = extVar cx1 q (VId va vx vz)
    checkType cx2 body
  _ -> do
    t <- inferD cx c
    case force cx t of
      VPi a1 f -> do
        if conv (cc cx) a1 va then ok else failWith "J: the motive has the wrong domain"
        let (cx1, vz) = extVar cx "$z" va
        case force cx1 (capp f vz) of
          VPi a2 g -> do
            if conv (cc cx1) a2 (VId va vx vz) then ok
              else failWith "J: the motive has the wrong second domain"
            let (cx2, vq) = extVar cx1 "$q" a2
            case force cx2 (capp g vq) of
              VU _ -> ok
              _    -> failWith "J: the motive does not land in a universe"
          _ -> failWith "J: the motive takes two arguments"
      _ -> failWith "J: the motive is not a function"

inferTel :: Cx -> Tel -> Res [Lvl]
inferTel _ [] = Right []
inferTel cx ((x, a) : tel) = do
  l  <- inferSort cx a
  ls <- inferTel (fst (extVar cx x (ev cx a))) tel
  Right (l : ls)

checkTelIn :: Cx -> Tel -> Val -> Res ()
checkTelIn _ [] _ = ok
checkTelIn cx ((x, a) : tel) t = do
  check cx a t
  checkTelIn (fst (extVar cx x (ev cx a))) tel t

checkStruct :: Cx -> [(Name, Exp)] -> Tel -> Env -> Res ()
checkStruct cx fs tel r
  | map fst fs /= map fst tel =
      failWith ("struct fields " ++ unwords (map fst fs) ++ " do not match " ++ unwords (map fst tel))
  | otherwise = go fs tel r
 where
  go [] [] _ = ok
  go ((l, e) : fs') ((_, a) : tel') r' = do
    check cx e (eval r' a)
    go fs' tel' (EVar r' l (ev cx e))
  go _ _ _ = failWith "struct: field mismatch"

fieldType :: Cx -> Val -> Tel -> Env -> Name -> Res Val
fieldType _ _ [] _ l = failWith ("no field " ++ l)
fieldType cx v ((l', a) : tel) r l
  | l == l'   = Right (eval r a)
  | otherwise = fieldType cx v tel (EVar r l' (vproj v l')) l

checkArgs :: Cx -> [Exp] -> Tel -> Env -> Res ()
checkArgs _ [] [] _ = ok
checkArgs cx (a : as) ((x, ta) : tel) r = do
  check cx a (eval r ta)
  checkArgs cx as tel (EVar r x (ev cx a))
checkArgs _ _ _ _ = failWith "constructor applied to the wrong number of arguments"

checkSplit :: Cx -> [(Name, ([Name], Exp))] -> [(Name, Tel)] -> Env -> Clos -> Res ()
checkSplit _ _ [] _ _ = ok
checkSplit cx bs ((c, tel) : cs) r f = case lookup c bs of
  Nothing -> failWith ("split: missing the branch for " ++ c)
  Just (xs, body) -> do
    (cx', vs) <- openTel cx xs tel r
    case check cx' body (capp f (VCon c vs)) of
      Left msg -> failWith ("in the branch  " ++ c ++ "  of the split:\n" ++ msg)
      Right () -> ok
    checkSplit cx bs cs r f

openTel :: Cx -> [Name] -> Tel -> Env -> Res (Cx, [Val])
openTel cx [] [] _ = Right (cx, [])
openTel cx (x : xs) ((y, ta) : tel) r = do
  let (cx', v) = extVar cx x (eval r ta)
  (cx'', vs) <- openTel cx' xs tel (EVar r y v)
  Right (cx'', v : vs)
openTel _ _ _ _ = failWith "split: a branch binds the wrong number of variables"

-- a let: a group of definitions, checked, then in scope
checkLocal :: Cx -> [Unit] -> Res Cx
checkLocal cx us = do
  let cx' = enterGroup cx us
  mapM_ (\u -> case u of
            UDef _ x a b _ -> do
              inCtx ("in the type of " ++ x) (checkType cx' a)
              inCtx ("in the definition of " ++ x) (check cx' b (ev cx' a))
            _ -> failWith "only definitions may appear in a let") us
  Right cx'

inCtx :: String -> Res a -> Res a
inCtx msg r = case r of
  Left m  -> Left (msg ++ ":\n" ++ m)
  Right a -> Right a

-- enter a mutual group: the members are in the environment and their
-- types in the context
enterGroup :: Cx -> [Unit] -> Cx
enterGroup cx us = cx { cxEnv = r, cxTys = [ (x, eval r a) | UDef _ x a _ _ <- us ] ++ cxTys cx }
 where r = mkGroup (cxEnv cx) us

------------------------------------------------------------------------
-- 10.  Modules: checking a module expression yields the module with its
-- instance.  Arguments are checked against the parameters in order; a
-- constraint of the module must be VALID for the arguments.

checkMod :: Cx -> MExp -> Res Mod
checkMod cx m = do
  md <- checkModHead cx m
  case modInst md of
    Just _  -> Right md
    Nothing -> failWith ("the module " ++ showM m ++ " needs arguments")

checkModHead :: Cx -> MExp -> Res Mod
checkModHead cx m = case m of
  MVar x -> lookupModCx cx x (cxEnv cx)
  MSub n x -> do
    md <- checkMod cx n
    lookupModCx cx x (instOf md)
  MApp n as -> do
    md <- checkModHead cx n
    case modInst md of
      Just _ | not (hasParams (modUnits md)) -> failWith ("the module " ++ showM n ++ " takes no arguments")
      _ -> do
        r <- checkInst cx (modEnv md) (modUnits md) as
        Right md { modInst = Just r }

lookupModCx :: Cx -> Name -> Env -> Res Mod
lookupModCx _ x r0 = go r0
 where
  go ENil = failWith ("unknown module " ++ x)
  go (EVar r _ _) = go r
  go (ELvl r _ _) = go r
  go (EDef r _ es _) = case lookup x es of
    Just (EMod md) -> Right md
    Just _         -> failWith (x ++ " is not a module")
    Nothing        -> go r

showM :: MExp -> String
showM m = case m of
  MVar x    -> x
  MSub n x  -> showM n ++ "." ++ x
  MApp n _  -> showM n ++ "[..]"

-- the arguments, against the parameters of the body, which is walked in
-- order and instantiated as it goes (Wang's checkInst, rule 3.5)
checkInst :: Cx -> Env -> [Unit] -> [Arg] -> Res Env
checkInst cx r0 us0 as0 = go r0 us0 as0
 where
  go r [] [] = Right r
  go _ [] _  = failWith "too many arguments for the module"
  go r (u : us) as = case (u, as) of
    (UPar _ x a, ATm e : as') -> do
      inCtx ("in the argument for " ++ x) (check cx e (eval r a))
      go (EVar r x (ev cx e)) us as'
    (UPar _ x _, _) -> failWith ("the module expects a term argument for " ++ x)
    (ULvl x, ALv l : as') -> do
      checkLv cx l
      go (ELvl r x (evalLv (cxEnv cx) l)) us as'
    (ULvl x, _) -> failWith ("the module expects a level argument for " ++ x)
    (UCstr cs, _) -> do
      let vs = map (evalCs r) cs
      if all (validCstr (cxTh cx)) vs then go r us as
        else failWith ("the arguments do not satisfy the constraint "
                       ++ commaSep [ prettyCs (csToCs c) | c <- vs ])
    (UDef{}, _) -> let (g, rest) = span isGroupUnit (u : us) in go (mkGroup r g) rest as
    (UMod{}, _) -> go (mkGroup r [u]) us as
    (UInst{}, _) -> go (mkGroup r [u]) us as
    _ -> go r us as

prettyCs :: Cs -> String
prettyCs (Cs l r m) = plv False l ++ (case r of REq -> " = "; RLe -> " <= "; RLt -> " < ") ++ plv False m

------------------------------------------------------------------------
-- 11.  Units.  Checking a list of units produces the extended context
-- and, LAZILY, one result per declaration: the context after a unit does
-- not depend on whether its body checked, so a driver can put a time
-- budget on each result and say which one failed or overran.

data Event = Event { evLabel :: String, evResult :: Res [String] }

checkUnits :: Cx -> [Unit] -> (Cx, [Event])
checkUnits cx us = let (cx', evs, _) = checkUnitsF cx us in (cx', evs)

-- the same, also returning the units with their hidden arguments filled:
-- a segment is built from its FILLED units, since its instances evaluate them
checkUnitsF :: Cx -> [Unit] -> (Cx, [Event], [Unit])
checkUnitsF cx [] = (cx, [], [])
checkUnitsF cx (u : us) = case u of
  ULvl x ->
    let cx' = cx { cxEnv = ELvl (cxEnv cx) x (lvar x), cxTh = addVar x (cxTh cx)
                 , cxLvls = x : cxLvls cx }
    in keep u (checkUnitsF cx' us)
  UCstr cs ->
    case mapM (checkCs cx) cs of
      Left msg -> let (cx', evs, us') = checkUnitsF cx us
                  in (cx', Event "constraint" (Left msg) : evs, u : us')
      Right vs ->
        let cx' = addCs cx vs
            note = [ "warning: the context now has a loop (everything collapses)"
                   | thLoop (cxTh cx'), not (thLoop (cxTh cx)) ]
            (cx'', evs, us') = checkUnitsF cx' us
        in (cx'', Event "constraint" (Right note) : evs, u : us')
  UPar i x a0 ->
    let fa = inCtx ("in the type of " ++ x) (fillT cx a0)
        a  = either (const a0) id fa
        va = ev cx a
        cx' = cx { cxEnv = EVar (cxEnv cx) x (etaV va (VConst i [])), cxTys = (x, va) : cxTys cx
                 , cxPSorts = (x, inferSort cx a) : cxPSorts cx }
        (cx'', evs, us') = checkUnitsF cx' us
    in (cx'', Event x (fmap (const []) (fa >> inCtx ("in the type of " ++ x) (checkType cx a))) : evs
       , UPar i x a : us')
  ULock s -> keep u (checkUnitsF cx { cxLocks = Set.fromList s } us)
  UDir d ->
    let (cx', evs, us') = checkUnitsF cx us
    in (cx', Event "#" (fillDir cx d >>= runDirective cx) : evs, u : us')
  UMod i x mus0 ds ->
    let -- the body is checked in the context where it is declared; its
        -- parameters are rigid there.  Locks set inside persist.  The
        -- universe of the segment as a type is computed from the sorts of
        -- its parameters; the sorts of nested segments are kept (stated
        -- with this segment's level parameters, found in an instance).
        (cxIn, evsIn, mus) = checkUnitsF cx { cxPSorts = [] } mus0
        u' = UMod i x mus ds
        cx1 = cx { cxEnv = mkGroup (cxEnv cx) [u'] }
        cx2 = cx1 { cxLocks = cxLocks cxIn, cxSegSort = (i, cxPSorts cxIn) : cxSegSort cxIn }
        (cx3, evs, us') = checkUnitsF cx2 us
    in (cx3, [ ev' { evLabel = x ++ "." ++ evLabel ev' } | ev' <- evsIn ] ++ evs, u' : us')
  UInst i x m0 ->
    let fm = fillM cx m0
        m  = either (const m0) id fm
        u' = UInst i x m
        cx1 = cx { cxEnv = mkGroup (cxEnv cx) [u'] }
        (cx2, evs, us') = checkUnitsF cx1 us
    in (cx2, Event x (fmap (const []) (fm >> checkMod cx m)) : evs, u' : us')
  UDef{} ->
    let (g0, rest) = span isGroupUnit (u : us)
        (g, cx1, ferrss) = fillGroupE cx g0
        evs1 = [ Event (unitName u0) (fmap (const []) (do
                   case ferrs of
                     (m : _) -> Left m
                     [] -> Right ()
                   case gu of
                     UDef _ x a b _ -> do
                       inCtx ("in the type of " ++ x) (checkType cx1 a)
                       inCtx ("in the definition of " ++ x) (check cx1 b (ev cx1 a))
                     _ -> Right ()))
               | (u0, gu, ferrs) <- zip3 g0 g ferrss ]
        (cx2, evs2, us') = checkUnitsF cx1 rest
    in (cx2, evs1 ++ evs2, g ++ us')
 where
  keep v (c, e, vs) = (c, e, v : vs)

fillDir :: Cx -> Directive -> Res Directive
fillDir cx d = case d of
  DNormal e -> fmap (DNormal . fst) (fillI cx e)
  DType e   -> fmap (DType . fst) (fillI cx e)
  DConv a b -> do (a', ta) <- fillI cx a
                  b' <- fillC cx b ta
                  Right (DConv a' b')
  DFails _  -> Right d

runDirective :: Cx -> Directive -> Res [String]
runDirective cx d = case d of
  DNormal e -> do
    _ <- inferD cx e
    Right ["#normal " ++ pretty e ++ "\n  = " ++ prettyAt 40 (rb True (cxLocks cx) (cxK cx) (ev cx e))]
  DType e -> do
    t <- inferD cx e
    Right ["#type " ++ pretty e ++ "\n  : " ++ prettyAt 40 (rb True (cxLocks cx) (cxK cx) t)]
  DConv a b -> do
    ta <- inferD cx a
    check cx b ta
    if conv (cc cx) (ev cx a) (ev cx b)
      then Right ["#conv " ++ pretty a ++ " == " ++ pretty b ++ "  ok"]
      else failWith ("#conv: not convertible:\n  " ++ pretty a ++ "\n  " ++ pretty b)
  DFails us ->
    let (_, evs) = checkUnits cx us
    in case [ m | Event _ (Left m) <- evs ] of
         (m : _) -> Right ["#fails ok: " ++ unwords (map (dropWhile (== ' ')) (lines m))]
         []      -> failWith "#fails: the block was accepted"

------------------------------------------------------------------------
-- 12.  Hidden arguments: the Agda-wiki design, without unification.
--
-- A declaration may have hidden binders  f {x : A} (y : B) : C ;  the
-- type is the ordinary  (x : A) -> (y : B) -> C.  Only USES of f are read
-- differently: the resolver puts a Hole at each hidden position (or the
-- given  {e} ), and this pass fills the holes before the core sees the
-- term.  A hole is filled by one-way MATCHING: the domain of a later
-- explicit argument, with the holes as rigid placeholders, against the
-- inferred type of that argument; then the result type against the
-- expected type, if there is one.  The solution, a value, is quoted back
-- into a term of the current scope.  Placeholders never escape one
-- application, nothing is postponed beyond it, and there is no unifier: a
-- hole that matching does not determine is an error ("give it as {e}").
-- Matching is deterministic and as simple as possible: structural, the
-- arguments of applications compared only under the same head, and no
-- definition unfolded, except the type computed to weak head normal form
-- where the pattern is a type former.  Two arguments that determine a hole
-- differently are an error, so the result never depends on the order.

hasHole :: Exp -> Bool
hasHole e = case e of
  Hole         -> True
  ProjU _ _    -> True
  Named _ _ a  -> hasHole a
  App a b      -> hasHole a || hasHole b
  Lam _ b      -> hasHole b
  Pi _ a b     -> hasHole a || hasHole b
  Let us b     -> any unitHole us || hasHole b
  Sum _ _ cs   -> any (any (hasHole . snd) . snd) cs
  Con _ as     -> any hasHole as
  Split _ _ bs -> any (hasHole . snd . snd) bs
  Sig _ a b    -> hasHole a || hasHole b
  Pair a b     -> hasHole a || hasHole b
  Fst a        -> hasHole a
  Snd a        -> hasHole a
  Rec tel      -> any (hasHole . snd) tel
  Struct fs    -> any (hasHole . snd) fs
  Proj a _     -> hasHole a
  Id a x y     -> any hasHole [a, x, y]
  Refl a       -> hasHole a
  IdJ a x c d y p -> any hasHole [a, x, c, d, y, p]
  LPi _ a      -> hasHole a
  LLam _ a     -> hasHole a
  LApp a _     -> hasHole a
  CPi _ a      -> hasHole a
  Acc m _      -> mHole m
  SegT m fs    -> mHole m || any (argHole . snd) fs
  New m        -> mHole m
  _            -> False
 where
  argHole (ATm a) = hasHole a
  argHole _       = False
  mHole m = case m of
    MVar _    -> False
    MSub n _  -> mHole n
    MApp n as -> mHole n || any argHole as

unitHole :: Unit -> Bool
unitHole u = case u of
  UDef _ _ a b _ -> hasHole a || hasHole b
  UPar _ _ a     -> hasHole a
  _              -> False

-- fill in checking mode
fillC :: Cx -> Exp -> Val -> Res Exp
fillC cx e t0
  | not (hasHole e) = Right e
  | otherwise = case (e, t) of
      (_, VCPi cs a) -> fillC (addCs cx cs) e a
      (Named i ds e', _) -> fmap (Named i ds) (fillC cx e' t0)
      (Lam x b, VPi a f) -> let (cx', v) = extVar cx x a in fmap (Lam x) (fillC cx' b (capp f v))
      (LLam x b, VLPi f) -> let (cx', l) = extLvl cx x in fmap (LLam x) (fillC cx' b (lcapp f l))
      (Pi x a b, VU _) -> do a' <- fillC cx a t
                             b' <- fillC (fst (extVar cx x (ev cx a'))) b t
                             Right (Pi x a' b')
      (Sig x a b, VU _) -> do a' <- fillC cx a t
                              b' <- fillC (fst (extVar cx x (ev cx a'))) b t
                              Right (Sig x a' b')
      (Rec tel, VU _) -> fmap Rec (fillTelIn cx tel t)
      (Sum i ds cs, VU _) -> fmap (Sum i ds) (mapM (\(c, tel) -> fmap ((,) c) (fillTelIn cx tel t)) cs)
      (Pair a b, VSig _ ta f) -> do a' <- fillC cx a ta
                                    b' <- fillC cx b (capp f (ev cx a'))
                                    Right (Pair a' b')
      (Struct fs, VRec _ tel r) -> fmap Struct (fillStruct fs tel r)
      (Con c as, VSum _ _ cs r) -> case lookup c cs of
        Just tel -> fmap (Con c) (fillArgs as tel r)
        Nothing  -> Right e
      (Split i ds bs, VPi dom f) -> case force cx dom of
        VSum _ _ cs r -> fmap (Split i ds) (mapM (fillBranch cs r f) bs)
        _ -> Right e
      (Refl a, VId ta _ _) -> fmap Refl (fillC cx a ta)
      (Let us b, _) -> do (us', cx') <- fillLocal cx us
                          fmap (Let us') (fillC cx' b t)
      _ | isApp e -> fmap fst (fillSpine cx e (Just t))
        | otherwise -> fmap fst (fillI cx e)
 where
  t = force cx t0
  fillStruct [] _ _ = Right []
  fillStruct ((l, a) : fs) ((_, ta) : tel) r = do
    a' <- fillC cx a (eval r ta)
    rest <- fillStruct fs tel (EVar r l (ev cx a'))
    Right ((l, a') : rest)
  fillStruct fs _ _ = Right fs
  fillArgs [] _ _ = Right []
  fillArgs (a : as) ((x, ta) : tel) r = do
    a' <- fillC cx a (eval r ta)
    rest <- fillArgs as tel (EVar r x (ev cx a'))
    Right (a' : rest)
  fillArgs as _ _ = Right as
  fillBranch cs r f (c, (xs, body)) = case lookup c cs of
    Nothing -> Right (c, (xs, body))
    Just tel -> do
      (cx', vs) <- openTel cx xs tel r
      body' <- fillC cx' body (capp f (VCon c vs))
      Right (c, (xs, body'))

isVar :: Exp -> Bool
isVar e = case e of
  Var _ -> True
  _     -> False

isApp :: Exp -> Bool
isApp e = case e of
  App _ _  -> True
  LApp _ _ -> True
  _        -> False

fillTelIn :: Cx -> Tel -> Val -> Res Tel
fillTelIn _ [] _ = Right []
fillTelIn cx ((x, a) : tel) t = do
  a' <- fillC cx a t
  rest <- fillTelIn (fst (extVar cx x (ev cx a'))) tel t
  Right ((x, a') : rest)

-- fill a type (possibly large)
fillT :: Cx -> Exp -> Res Exp
fillT cx e
  | not (hasHole e) = Right e
  | otherwise = case e of
      Named i ds e' -> fmap (Named i ds) (fillT cx e')
      Pi x a b -> do a' <- fillT cx a
                     b' <- fillT (fst (extVar cx x (ev cx a'))) b
                     Right (Pi x a' b')
      Sig x a b -> do a' <- fillT cx a
                      b' <- fillT (fst (extVar cx x (ev cx a'))) b
                      Right (Sig x a' b')
      LPi x a -> fmap (LPi x) (fillT (fst (extLvl cx x)) a)
      CPi cs a -> fmap (CPi cs) (fillT (addCs cx (map (evalCs (cxEnv cx)) cs)) a)
      Let us b -> do (us', cx') <- fillLocal cx us
                     fmap (Let us') (fillT cx' b)
      _ -> fmap fst (fillI cx e)

-- fill in inference mode; returns the filled term and its type
fillI :: Cx -> Exp -> Res (Exp, Val)
fillI cx e
  | not (hasHole e) = do t <- inferD cx e; Right (e, t)
  | otherwise = case e of
      _ | isApp e -> fillSpine cx e Nothing
      Named{} -> retype (fillT cx e)
      Pi{}   -> retype (fillT cx e)
      Sig{}  -> retype (fillT cx e)
      Id a x y -> do
        (a', _) <- fillI cx a
        let va = ev cx a'
        x' <- fillC cx x va
        y' <- fillC cx y va
        retype (Right (Id a' x' y'))
      Refl a -> do (a', _) <- fillI cx a; retype (Right (Refl a'))
      Fst a  -> do (a', _) <- fillI cx a; retype (Right (Fst a'))
      Snd a  -> do (a', _) <- fillI cx a; retype (Right (Snd a'))
      Proj a l -> do (a', _) <- fillI cx a; retype (Right (Proj a' l))
      -- a defined member of a NEUTRAL element  (S k).g : evaluation is
      -- untyped, so the member is taken in the eta-expanded element
      --   (new M[(S k).f1, .., (S k).fn]).g
      -- which unfolds; a field stays a projection
      ProjU a l -> do
        (a', ta) <- fillI cx a
        case force cx ta of
          VSegT md fs
            | Just (UDef{}) <- memberUnit (modUnits md) l
            , Nothing <- quote cx (VSegT md [])
            , not (isVar a') ->
                failWith ("the member " ++ l ++ " of " ++ pretty a' ++ " would not unfold: its segment "
                          ++ shortId (modId md) ++ " cannot be named here (bring it into scope)")
          VSegT md fs
            | Just (UDef{}) <- memberUnit (modUnits md) l
            , Just (SegT me _) <- quote cx (VSegT md []) ->
                do args <- mapM (\p -> case lookup p fs of
                                   Just (VLvl lv) -> maybe (Left ("cannot write the level of " ++ p)) (Right . ALv)
                                                           (quote cx (VU lv) >>= \u -> case u of { U lv' -> Just lv'; _ -> Nothing })
                                   Just v -> maybe (Left ("cannot write the field " ++ p)) (Right . ATm) (quote cx v)
                                   Nothing -> Right (ATm (Proj a' p))) (paramNames (modUnits md))
                   retype (Right (Proj (New (MApp me args)) l))
          _ -> retype (Right (Proj a' l))
      Let us b -> do (us', cx') <- fillLocal cx us
                     (b', _) <- fillI cx' b
                     retype (Right (Let us' b'))
      IdJ a x c d y p -> do
        (a', _) <- fillI cx a
        let va = ev cx a'
            vx = ev cx x
        x' <- fillC cx x va
        c' <- case c of
          Lam z (Lam q body) -> do
            let (cx1, vz) = extVar cx z va
                (cx2, _)  = extVar cx1 q (VId va vx vz)
            fmap (Lam z . Lam q) (fillT cx2 body)
          _ -> fmap fst (fillI cx c)
        let vc = ev cx c'
        d' <- fillC cx d (app (app vc vx) (VRefl vx))
        y' <- fillC cx y va
        p' <- fillC cx p (VId va vx (ev cx y'))
        retype (Right (IdJ a' x' c' d' y' p'))
      Acc m x -> do m' <- fillM cx m; retype (Right (Acc m' x))
      SegT m fs -> do m' <- fillM cx m
                      md <- checkModHead cx m'
                      fs' <- fillInst cx (modEnv md) (modUnits md) [ (Just x, a) | (x, a) <- fs ]
                      retype (Right (SegT m' [ (x, a) | (Just x, a) <- fs' ]))
      New m -> do m' <- fillM cx m; retype (Right (New m'))
      _ -> failWith ("cannot infer the hidden arguments in  " ++ pretty e
                     ++ "\n  (give a type, or the arguments as {e})")
 where
  retype r = do e' <- r; t <- inferD cx e'; Right (e', t)

fillArg :: Cx -> Arg -> Res Arg
fillArg cx (ATm a)
  | hasHole a = fmap (ATm . fst) (fillI cx a)
  | otherwise = Right (ATm a)
fillArg _ a = Right a

fillM :: Cx -> MExp -> Res MExp
fillM cx m = case m of
  MVar _    -> Right m
  MSub n x  -> fmap (\n' -> MSub n' x) (fillM cx n)
  MApp n as
    | not (any argH as) -> fmap (\n' -> MApp n' as) (fillM cx n)
    | otherwise -> do
        n' <- fillM cx n
        md <- checkModHead cx n'
        as' <- fillInst cx (modEnv md) (modUnits md) (map ((,) Nothing) as)
        Right (MApp n' (map snd as'))
 where argH (ATm a) = hasHole a
       argH _ = False

-- arguments against the parameters of a segment body, in order, each
-- filled against its parameter's type (so a lambda gets its expected type);
-- named arguments (segment types M[x := e]) are matched by name
fillInst :: Cx -> Env -> [Unit] -> [(Maybe Name, Arg)] -> Res [(Maybe Name, Arg)]
fillInst cx r0 us0 as0 = go r0 us0 as0
 where
  named = any ((/= Nothing) . fst) as0
  go _ [] _ = Right []
  go _ _ [] | not named = Right []
  go r (u : us) as = case u of
    UPar i x a ->
      let (mine, rest) = if named then ([ p | p@(Just y, _) <- as, y == x ], as)
                                  else (take 1 as, drop 1 as)
      in case mine of
        ((n, ATm e) : _) -> do
          e' <- inCtx ("in the argument for " ++ x) (fillC cx e (eval r a))
          more <- go (EVar r x (ev cx e')) us rest
          Right ((n, ATm e') : more)
        ((n, ALv l) : _) -> do
          more <- go r us rest
          Right ((n, ALv l) : more)
        [] -> go (EVar r x (VConst ("?" ++ i) [])) us rest
    ULvl x ->
      let (mine, rest) = if named then ([ p | p@(Just y, _) <- as, y == x ], as)
                                  else (take 1 as, drop 1 as)
      in case mine of
        ((n, ALv l) : _) -> do
          more <- go (ELvl r x (evalLv (cxEnv cx) l)) us rest
          Right ((n, ALv l) : more)
        (p : _) -> do more <- go r us rest; Right (p : more)
        [] -> go r us rest
    UDef{} -> let (g, rest) = span isGroupUnit (u : us) in go (mkGroup r g) rest as
    UMod{} -> go (mkGroup r [u]) us as
    UInst{} -> go (mkGroup r [u]) us as
    _ -> go r us as

-- a let / where group, filled in its own (lazy) context
fillLocal :: Cx -> [Unit] -> Res ([Unit], Cx)
fillLocal cx us = do
  let (us', cx', errs) = fillGroup cx us
  case errs of
    (m : _) -> Left m
    []      -> Right (us', cx')

-- A mutual group: the filled units are tied in a knot with the context
-- they are filled in, so a member can be used (lazily) while its siblings
-- are filled.  On an error the unit keeps its unfilled form and the error
-- is reported.
fillGroup :: Cx -> [Unit] -> ([Unit], Cx, [String])
fillGroup cx us = let (us', cx1, errss) = fillGroupE cx us in (us', cx1, concat errss)

-- the same, with the errors per unit (forced only when that unit's own
-- event is, so the driver's time budget covers the filling too)
fillGroupE :: Cx -> [Unit] -> ([Unit], Cx, [[String]])
fillGroupE cx us = (us', cx1, map (snd . snd) res)
 where
  res = [ (u, fill u) | u <- us ]
  fill u = case u of
    UDef i x a b ds ->
      let ta = inCtx ("in the type of " ++ x) (fillT cx1 a)
          a' = either (const a) id ta
          tb = inCtx ("in the definition of " ++ x) (fillC cx1 b (ev cx1 a'))
      in (UDef i x a' (either (const b) id tb) ds, [ m | Left m <- [ta] ] ++ [ m | Left m <- [tb] ])
    _ -> (u, [])
  us'  = [ fst r | (_, r) <- res ]
  cx1  = enterGroup cx us'

-- An application spine with holes.  Pass 1 walks the head's type with
-- the holes as rigid placeholders and matches; the solutions are quoted;
-- pass 2 rebuilds the spine and fills the arguments that could not be
-- inferred, against their now known domains.  The core infers the type.
fillSpine :: Cx -> Exp -> Maybe Val -> Res (Exp, Val)
fillSpine cx e mexp = do
  let (h, args) = spineOf e []
  (h', th) <- fillI cx h
  (sols', pre) <- rounds th args [] (0 :: Int)
  -- a second solution that can be written here must agree with the first
  -- (cheap tests first: conversion with the locks, then without them, since
  -- a lock is a strategy; only then whether both can be written here)
  case [ (n, qv, qw) | ('!' : n, w) <- sols', Just v <- [lookup n sols']
           , not (conv (cc cx) v w), not (conv ((cc cx) { ccS = Set.empty }) v w)
           , Just qv <- [quoteWith sc v], Just qw <- [quoteWith sc w] ] of
    ((n, qv, qw) : _) -> failWith ("hidden argument " ++ show (1 + read (drop 2 n) :: Int) ++ " of " ++ pretty h
                         ++ " is determined differently by two arguments:\n    " ++ pretty qv
                         ++ "\n  and\n    " ++ pretty qw ++ "\n  give it as {e}")
    [] -> Right ()
  qs <- mapM (\(i, _) -> case lookup (hole i) sols' of
                 Just v  -> case firstJust [ quoteWith sc { scUnfold = False } v
                                           , quoteWith scDeep { scUnfold = False } v
                                           , quoteWith sc v ] of
                   Just q  -> Right (i, q)
                   Nothing -> failWith ("hidden argument " ++ show (i + 1) ++ " of " ++ pretty h
                                        ++ " was found, but it cannot be written in this scope: "
                                        ++ "no name for  " ++ take 300 (quoteBlame cx v)
                                        ++ "\n  give it as {e}")
                 Nothing -> failWith ("cannot infer hidden argument " ++ show (i + 1) ++ " of "
                                      ++ pretty h ++ "; give it as {e}\n  in  " ++ take 300 (pretty e)))
             [ p | p@(_, Nothing) <- pre ]
  -- the type comes from walking the head's type with the actual
  -- arguments: asking the core to infer the filled spine again would
  -- re-check every nested application at every level (quadratic in a
  -- transH chain, and it re-checks module arguments each time)
  (e', t) <- pass2 h' th (zip [0 ..] args) pre qs
  Right (e', dischargeT t)
 where
  hole i = "?m" ++ show i
  sc = scopeOf cx
  -- a solution is written with names only, searching instances inside
  -- instances to depth 3, then to depth 6; only then may a definition with
  -- no name be written as its body (which is costly)
  scDeep = scopeWith True cx
  firstJust xs = case [ x | Just x <- xs ] of { (x : _) -> Just x; [] -> Nothing }
  -- each explicit argument is inferred ONCE (lazily), whatever the number
  -- of rounds: re-filling nested applications per round is exponential
  inferred = [ (i, fillI cx x) | (i, Left x) <- zip [0 :: Int ..] (snd (spineOf e [])), x /= Hole ]
  spineOf (App a b) as  = spineOf a (Left b : as)
  spineOf (LApp a l) as = spineOf a (Right l : as)
  spineOf x as          = (x, as)
  -- discharge constraint products along the way
  pi' t = case force cx t of
    VCPi cs a | all (validCstr (cxTh cx)) cs -> pi' a
    t' -> t'
  -- Pass 1 is repeated while it finds new solutions: a solved hole is
  -- walked with its solution, so a later round can check an argument that
  -- could not be inferred (a lambda) against its now known domain, and the
  -- type of an over-applied result (F y) is known.  Still one application,
  -- still no unification.
  rounds th args sols n = do
    (sols1, pre, rt) <- pass1 sols th args 0 sols
    -- the expected type only fills holes the arguments left open: where
    -- both determine a hole, the arguments decide (a definition need not be
    -- injective, so f ?y against f t need not give ?y = t)
    let sols2 = case mexp of
          Nothing -> sols1
          Just t -> let new = match cx rt t sols1
                        added = take (length new - length sols1) new
                    in [ p | p@(n, _) <- added, take 1 n /= "!" ] ++ sols1
    let nsol = length . filter ((/= '!') . head . fst)
    if nsol sols2 > nsol sols && n < 8 then rounds th args sols2 (n + 1)
      else Right (sols2, pre)
  -- per argument: Nothing = a hole, Just (Left x') = filled, Just (Left
  -- Hole) = an explicit argument not yet filled (pass 2 checks it)
  pass1 _ th [] _ sols = Right (sols, [], th)
  pass1 known th (a : as) i sols = case (a, pi' th) of
    (Right l, VLPi f) -> do
      (s, pre, rt) <- pass1 known (lcapp f (evalLv (cxEnv cx) l)) as (i + 1) sols
      Right (s, (i, Just (Right l)) : pre, rt)
    (Left Hole, VPi _ f) -> do
      let v = fromMaybe (VConst (hole i) []) (lookup (hole i) known)
      (s, pre, rt) <- pass1 known (capp f v) as (i + 1) sols
      Right (s, (i, Nothing) : pre, rt)
    (Left x, VPi dom f) -> case fromMaybe (fillI cx x) (lookup i inferred) of
      Right (x', tx) -> do
        let sols1 = match cx dom tx sols
        (s, pre, rt) <- pass1 known (capp f (ev cx x')) as (i + 1) sols1
        Right (s, (i, Just (Left x')) : pre, rt)
      Left _
        -- a lambda whose domain is known: infer its body, and match the
        -- codomain (a solution mentioning the bound variable will not quote)
        | Lam z body <- x, VPi a cl <- pi' dom, not (hasPlaceholder a)
        , let (cxz, vz) = extVar cx z a
        , Right (body', tb) <- fillI cxz body -> do
            let sols1 = match cxz (capp cl vz) tb sols
                x' = Lam z body'
            (s, pre, rt) <- pass1 known (capp f (ev cx x')) as (i + 1) sols1
            Right (s, (i, Just (Left x')) : pre, rt)
      Left _ -> case fillC cx x dom of
        Right x' | not (hasPlaceholder dom) -> do
          (s, pre, rt) <- pass1 known (capp f (ev cx x')) as (i + 1) sols
          Right (s, (i, Just (Left x')) : pre, rt)
        _ -> do
          (s, pre, rt) <- pass1 known (capp f (VConst ("?p" ++ show i) [])) as (i + 1) sols
          Right (s, (i, Just (Left Hole)) : pre, rt)
    (_, t') | isPH (headV t') ->
      -- the type is not known yet: stop here, a later round continues
      Right (sols, [ (j, Just (Left Hole)) | (j, _) <- zip [i ..] (a : as) ], th)
    (_, t') -> failWith ("too many arguments for " ++ pretty e ++ "\n  at type " ++ showV cx t')
  headV v = case v of
    VApp f _ -> headV f
    VFst a -> headV a
    VSnd a -> headV a
    VProj a _ -> headV a
    _ -> v
  isPH v = case v of
    VConst n _ -> take 2 n == "?p" || take 2 n == "?m"
    _ -> False
  -- does a domain still mention a placeholder?  (a shallow search: it
  -- only decides whether to check an argument now or in a later round)
  hasPlaceholder d = ph (3 :: Int) d
  ph 0 _ = False
  ph n v = case v of
    VConst c _ -> isPH (VConst c [])
    VApp f a -> ph n f || ph n a
    VPi a f -> ph n a || ph (n - 1) (capp f (VGen (-1)))
    VSig _ a f -> ph n a || ph (n - 1) (capp f (VGen (-1)))
    VId a x y -> ph n a || ph n x || ph n y
    VDef _ d sp _ _ -> any (ph n) d || any (\el -> case el of { EApp a -> ph n a; _ -> False }) sp
    VSegT _ fs -> any (ph n . snd) fs
    VFst a -> ph n a
    VSnd a -> ph n a
    VProj a _ -> ph n a
    VPair a b -> ph n a || ph n b
    VCon _ as -> any (ph n) as
    _ -> False
  -- pass 2: rebuild, filling postponed explicit arguments by checking
  dischargeT t = case force cx t of
    VCPi cs a | all (validCstr (cxTh cx)) cs -> dischargeT a
    _ -> t
  pass2 acc th [] _ _ = Right (acc, th)
  pass2 acc th ((i, a) : as) pre qs = case (a, pi' th, lookup i pre) of
    (Right l, VLPi f, _) -> pass2 (LApp acc l) (lcapp f (evalLv (cxEnv cx) l)) as pre qs
    (Left Hole, VPi _ f, Just Nothing) -> do
      let q = fromMaybe Hole (lookup i qs)
      pass2 (App acc q) (capp f (ev cx q)) as pre qs
    (Left x, VPi dom f, Just (Just (Left Hole))) -> do
      x' <- fillC cx x dom
      pass2 (App acc x') (capp f (ev cx x')) as pre qs
    (Left _, VPi _ f, Just (Just (Left x'))) -> pass2 (App acc x') (capp f (ev cx x')) as pre qs
    _ -> failWith ("hidden arguments: malformed application " ++ pretty e)

-- one-way matching of a pattern (containing placeholders ?m.. ) against a
-- value, structurally and WITHOUT unfolding definitions: where the heads
-- differ nothing is learnt.  Adds solutions, never fails (a mismatch is
-- left to the core); a second solution for a placeholder is recorded
-- (!?m..), and fillSpine checks that it agrees with the first
match :: Cx -> Val -> Val -> [(Id, Val)] -> [(Id, Val)]
match cx p0 t0 sols0 = go (cxK cx) p0 t0 sols0
 where
  go k p t sols = case (p, t) of
    -- a solution mentioning a variable bound inside the pattern fails to
    -- quote; a second, different solution is recorded as a conflict (the
    -- result must not depend on the order in which arguments are read)
    (VConst n [], _) | take 2 n == "?m" -> case lookup n sols of
      Nothing -> (n, t) : sols
      Just _ | k == cxK cx -> ('!' : n, t) : sols
             | otherwise -> sols
    (VPi a f, VPi b g)     -> under k f g (go k a b sols)
    (VSig _ a f, VSig _ b g) -> under k f g (go k a b sols)
    (VId a x y, VId b x' y') -> go k y y' (go k x x' (go k a b sols))
    (VRefl a, VRefl b)     -> go k a b sols
    -- an application: the arguments are matched only under the same
    -- head with the same number of arguments (matching arguments under
    -- different heads would invent solutions)
    (VApp _ _, VApp _ _)
      | (hp, ap) <- spineV p [], (ht, at) <- spineV t [], length ap == length at
      , Just sols1 <- sameHead k hp ht sols -> goList k ap at sols1
      | otherwise -> sols
    (VCon c as, VCon d bs) | c == d -> goList k as bs sols
    (VPair a b, VPair a' b') -> go k b b' (go k a a' sols)
    -- a projection of a hole determines only part of it (?m.1 = s.1 does
    -- not give ?m = s): nothing is learnt through a projection of a hole
    (VFst a, VFst b)       | not (isHoleV a) -> go k a b sols
    (VSnd a, VSnd b)       | not (isHoleV a) -> go k a b sols
    (VProj a l, VProj b l') | l == l' && not (isHoleV a) -> go k a b sols
    (VLApp a _, VLApp b _) -> go k a b sols
    (VDef i d sp _ _, VDef j d' sp' _ _) | i == j && length sp == length sp' ->
      goSp k sp sp' (goList k d d' sols)
    (VSegT m fs, VSegT n gs) | modId m == modId n ->
      goList k (map snd fs) (map snd gs) (goList k (modDyn m) (modDyn n) sols)
    (VNamedE _ _ a, _) -> go k a t sols
    (_, VNamedE _ _ b) -> go k p b sols
    (VInst m r, VInst n r') | modId m == modId n ->
      goList k [ lookupDyn r x | x <- paramNames (modUnits m) ]
               [ lookupDyn r' x | x <- paramNames (modUnits n) ] sols
    (VSum i d _ _, VSum j d' _ _) | i == j -> goList k d d' sols
    -- different heads: the two sides are computed to weak head normal
    -- form (a type is computed, never guessed), and compared again if one
    -- of them changed; otherwise nothing is learnt
    _ | t' <- whnf (cxLocks cx) t, p' <- whnf (cxLocks cx) p
      , progressed t t' || progressed p p' -> go k p' t' sols
      | otherwise -> sols
  isHoleV x = case x of
    VConst n [] -> take 2 n == "?m"
    _ -> False
  spineV v as = case v of
    VApp f a -> spineV f (a : as)
    _ -> (v, as)
  -- did weak head normalisation compute something (a definition unfolded,
  -- a projection or an application reduced)?
  progressed a b = case (a, b) of
    (VDef{}, VDef{}) -> False
    (VApp{}, VApp{}) -> False
    (VFst{}, VFst{}) -> False
    (VSnd{}, VSnd{}) -> False
    (VProj{}, VProj{}) -> False
    (VIdJ{}, VIdJ{}) -> False
    (VLApp{}, VLApp{}) -> False
    (VDef{}, _) -> True
    (VApp{}, _) -> True
    (VFst{}, _) -> True
    (VSnd{}, _) -> True
    (VProj{}, _) -> True
    (VIdJ{}, _) -> True
    (VLApp{}, _) -> True
    _ -> False
  sameHead k hp ht sols = case (hp, ht) of
    (VGen i, VGen j) | i == j -> Just sols
    (VConst a [], VConst b []) | a == b && not (isHoleV hp) -> Just sols
    (VDef i _ _ _ _, VDef j _ _ _ _) | i == j -> Just (go k hp ht sols)
    (VProj a l, VProj b l') | l == l' && not (isHoleV a) -> Just (go k a b sols)
    (VFst a, VFst b) | not (isHoleV a) -> Just (go k a b sols)
    (VSnd a, VSnd b) | not (isHoleV a) -> Just (go k a b sols)
    (VNamedE _ _ a, _) -> sameHead k a ht sols
    (_, VNamedE _ _ b) -> sameHead k hp b sols
    _ -> Nothing
  goList k as bs sols = foldl (\acc (a, b) -> go k a b acc) sols (zip as bs)
  goSp k sp sp' sols = foldl step sols (zip sp sp')
   where step acc (EApp a, EApp b) = go k a b acc
         step acc _ = acc
  under k f g sols = go (k + 1) (capp f (VGen k)) (capp g (VGen k)) sols

pname :: (Name, [Unit], Maybe Env) -> Name
pname (x, _, _) = x

-- a segment in scope and its submodules, with their paths (depth 3)
segPaths :: Id -> [(Name, [Unit], Maybe Env)] -> [(Id, [(Name, [Unit], Maybe Env)])]
segPaths i path
  | length path > 3 = []
  | otherwise = (i, path) : concat [ segPaths j (path ++ [(y, us, Nothing)])
                                   | UMod j y us _ <- units (last path) ]
 where units (_, us, _) = us

-- Quoting: a value back to a term of the current scope.  Variables are
-- named by their binders, parameters by their names, glued constants by a
-- name in scope (or a member of a module in scope) whose dynamic part
-- agrees.  Fails rather than guess.
data QScope = QScope
  { scGens   :: [(Int, Name)]
  , scConsts :: [(Id, Name)]
  , scLvls   :: [(LName, Name)]
  , scDefs   :: [(Id, [Val], Exp)]
  , scMods   :: [(Id, [Val], MExp)]     -- a segment is its id AND its dynamic part
  , scDefsIx :: [Map.Map Id [([Val], Exp)]]   -- the same, indexed by id, per
  , scModsIx :: [Map.Map Id [([Val], MExp)]]  -- environment node (inner first)
  , scUnfold :: Bool    -- a definition with no name: write its body instead
  , scCC     :: CC
  , scK      :: Int
  , scEnv    :: Env
  , scEtas   :: [(Val, Name)]       -- variables bound to eta-expanded instances
  , scSegs   :: [(Id, [(Name, [Unit], Maybe Env)])] }
      -- segments in scope, by path; Just r: already instantiated (by r)

-- the naming information contributed by one group of definitions: built
-- lazily ONCE per environment node, and shared by every quotation
data QFrag = QFrag
  { fDefs :: [(Id, [Val], Exp)]
  , fMods :: [(Id, [Val], MExp)]
  , fSegs :: [(Id, [(Name, [Unit], Maybe Env)])]
  , fDeep :: ([(Id, [Val], Exp)], [(Id, [Val], MExp)])
      -- the same, with instances declared inside instances searched deeper
  , fIx :: (Map.Map Id [([Val], Exp)], Map.Map Id [([Val], MExp)])
  , fDeepIx :: (Map.Map Id [([Val], Exp)], Map.Map Id [([Val], MExp)]) }
      -- the tables indexed by id (built lazily, once per node)

fragOf :: [(Name, Ent)] -> QFrag
fragOf es = QFrag ds ms (concatMap g es) (dds, dms) (ix ds, ix ms) (ix dds, ix dms)
 where
  ds = concatMap (d 3) es
  ms = concatMap (m 3) es
  dds = concatMap (d 6) es
  dms = concatMap (m 6) es
  -- per id, the entries in their original order
  ix xs = Map.fromListWith (\new old -> old ++ new) [ (i, [(dy, h)]) | (i, dy, h) <- xs ]
  d _ (x, EVal (VDef i dy [] _ _)) = [(i, dy, Var x)]
  d n (x, EMod md) = instDefs (n :: Int) (MVar x) md
  d _ _ = []
  m n (x, EMod md) = instMods (n :: Int) (MVar x) md
  m _ _ = []
  g (x, EMod md) = segPaths (modId md) [(x, modUnits md, modInst md)]
  g _ = []
  -- a module reached by me: if instantiated, its definitions, its
  -- submodules (as segment types), and recursively the instances it
  -- declares (module BX = .. inside it)
  instDefs n me md = case modInst md of
    Nothing -> []
    Just r -> [ (i, dy, Acc me y) | UDef _ y _ _ _ <- modUnits md
                                  , VDef i dy [] _ _ <- [lookupVal r y] ]
              ++ (if n <= 0 then [] else
                    concat [ instDefs (n - 1) (MSub me y) (lookupMod r y) | UInst _ y _ <- modUnits md ])
  instMods n me md = (modId md, modDyn md, me) : case modInst md of
    Nothing -> []
    Just r -> [ (i, modDyn (lookupMod r y), MSub me y) | UMod i y _ _ <- modUnits md ]
              ++ (if n <= 0 then [] else
                    concat [ instMods (n - 1) (MSub me y) (lookupMod r y) | UInst _ y _ <- modUnits md ])

scopeOf :: Cx -> QScope
scopeOf = scopeWith False

-- deep: instances declared inside instances searched to depth 6, not 3
scopeWith :: Bool -> Cx -> QScope
scopeWith deep cx = go (cxEnv cx) [] (QScope [] [] [] [] [] [] [] True (cc cx) (cxK cx) (cxEnv cx) [] [])
 where
  -- variables are collected as we walk; the definitions' parts are the
  -- nodes' fragments, concatenated lazily (inner first)
  go r frags sc = case r of
    ENil -> sc { scDefs = concatMap (if deep then fst . fDeep else fDefs) (reverse frags)
               , scMods = concatMap (if deep then snd . fDeep else fMods) (reverse frags)
               , scDefsIx = map (fst . (if deep then fDeepIx else fIx)) (reverse frags)
               , scModsIx = map (snd . (if deep then fDeepIx else fIx)) (reverse frags)
               , scSegs = concatMap fSegs (reverse frags) }
    EVar r' x v -> go r' frags (addVar' x v sc)
    ELvl r' x l -> go r' frags (case latoms l of
                                  [(n, 0)] -> sc { scLvls = scLvls sc ++ [(n, x)] }
                                  _ -> sc)
    EDef r' _ _ fr -> go r' (fr : frags) sc
  addVar' x v sc = case v of
    VGen i     -> sc { scGens = scGens sc ++ [(i, x)] }
    VConst i _ -> sc { scConsts = scConsts sc ++ [(i, x)] }
    -- an eta-expanded variable: its base names the variable (for its
    -- projections x.f), and the whole instance is the variable itself
    VInst m r  -> let sc1 = sc { scEtas = scEtas sc ++ [(v, x)] }
                  in case [ b | p <- termParams (modUnits m), VProj b q <- [lookupDyn r p], q == p ] of
                       (VConst i _ : _) -> sc1 { scConsts = scConsts sc1 ++ [(i, x)] }
                       (VGen i : _)     -> sc1 { scGens = scGens sc1 ++ [(i, x)] }
                       _ -> sc1
    _ -> sc

lookupAnyE :: Env -> Name -> Maybe (Either Val Mod)
lookupAnyE r0 x = go r0
 where
  go ENil = Nothing
  go (EVar r y v) = if x == y then Just (Left v) else go r
  go (ELvl r y l) = if x == y then Just (Left (VLvl l)) else go r
  go (EDef r _ es _) = case lookup x es of
    Just (EVal v) -> Just (Left v)
    Just (EMod m) -> Just (Right m)
    Nothing       -> go r

-- the names occurring free in an expression (variables, levels, module heads)
freeNamesE :: Exp -> [Name]
freeNamesE e0 = go [] e0
 where
  go bs e = case e of
    Var x        -> [ x | x `notElem` bs ]
    U l          -> lv bs l
    App a b      -> go bs a ++ go bs b
    Lam x b      -> go (x : bs) b
    Pi x a b     -> go bs a ++ go (x : bs) b
    Sig x a b    -> go bs a ++ go (x : bs) b
    Named _ _ a  -> go bs a
    Let us b     -> let bs' = [ unitName u | u <- us ] ++ bs
                    in concat [ go bs' a ++ go bs' t | UDef _ _ a t _ <- us ] ++ go bs' b
    Sum _ _ cs   -> concat [ tel bs t | (_, t) <- cs ]
    Con _ as     -> concatMap (go bs) as
    Split _ _ br -> concat [ go (xs ++ bs) b | (_, (xs, b)) <- br ]
    Pair a b     -> go bs a ++ go bs b
    Fst a        -> go bs a
    Snd a        -> go bs a
    Rec t        -> tel bs t
    Struct fs    -> concatMap (go bs . snd) fs
    Proj a _     -> go bs a
    ProjU a _    -> go bs a
    Id a x y     -> go bs a ++ go bs x ++ go bs y
    Refl a       -> go bs a
    IdJ a x c d y p -> concatMap (go bs) [a, x, c, d, y, p]
    LPi x a      -> go (x : bs) a
    LLam x a     -> go (x : bs) a
    LApp a l     -> go bs a ++ lv bs l
    CPi cs a     -> concat [ lv bs l ++ lv bs m | Cs l _ m <- cs ] ++ go bs a
    Acc m _      -> me bs m
    SegT m fs    -> me bs m ++ concat [ arg bs a | (_, a) <- fs ]
    New m        -> me bs m
    Hole         -> []
  tel _ [] = []
  tel bs ((x, a) : t) = go bs a ++ tel (x : bs) t
  lv bs l = case l of
    LV x     -> [ x | x `notElem` bs ]
    LSuc m   -> lv bs m
    LMax a b -> lv bs a ++ lv bs b
    LZero    -> []
  arg bs (ATm a) = go bs a
  arg bs (ALv l) = lv bs l
  me bs m = case m of
    MVar x    -> [ x | x `notElem` bs ]
    MSub n _  -> me bs n
    MApp n as -> me bs n ++ concatMap (arg bs) as

quote :: Cx -> Val -> Maybe Exp
quote cx = quoteWith (scopeOf cx)

-- the first subvalue that cannot be named (for the error message)
quoteBlame :: Cx -> Val -> String
quoteBlame cx v0 = go (scopeOf cx) v0
 where
  go sc v = case quoteWith sc v of
    Just _ -> ""
    Nothing -> case [ b | w <- kids v, let b = go sc w, b /= "" ] of
      (b : _) -> b
      [] -> showV cx v
  kids v = case v of
    VApp f a -> [f, a]
    VDef _ _ sp _ _ -> [ a | EApp a <- sp ]
    VInst m r -> [ lookupDyn r x | x <- termParams (modUnits m) ]
    VNamedE _ _ a -> [a]
    VPi a _ -> [a]
    VSig _ a _ -> [a]
    VId a x y -> [a, x, y]
    VPair a b -> [a, b]
    VFst a -> [a]
    VSnd a -> [a]
    VProj a _ -> [a]
    VCon _ as -> as
    _ -> []

quoteWith :: QScope -> Val -> Maybe Exp
quoteWith sc v0 = case v0 of
  VGen i -> fmap Var (lookup i (scGens sc))
  VConst i [] -> fmap Var (lookup i (scConsts sc))
  VU l -> fmap U (qLvl l)
  VLvl _ -> Nothing
  VDef i d sp u encl -> case [ h | t <- scDefsIx sc, (d', h) <- Map.findWithDefault [] i t, convs (scCC sc) d d' ] of
    (h : _) -> qSpine h (reverse sp)
    [] -> case [ h | (m, path) <- scSegs sc, Just h <- [viaSeg m path i d encl] ] of
      (h : _) -> qSpine h (reverse sp)
      [] | scUnfold sc -> quoteWith sc (whnf Set.empty (VDef "" [] [] u []))
         | otherwise -> Nothing
  VApp f a -> App <$> q f <*> q a
  VPi a f -> binder (\x b -> Pi x <$> q a <*> b) f
  VSig (Just (i, ds, d)) a (Clos x e r)
    | convs (scCC sc) d (map (lookupDyn (scEnv sc)) ds)
    , freeHere (filter (/= x) (freeNamesE e)) r ->
        (\a' -> Named i ds (Sig x a' e)) <$> q a
    | otherwise -> Nothing
  VRec (Just (i, ds, d)) t r
    | convs (scCC sc) d (map (lookupDyn (scEnv sc)) ds)
    , freeHere (freeNamesE (Rec t)) r -> Just (Named i ds (Rec t))
    | otherwise -> Nothing
  VSig Nothing a f -> binder (\x b -> Sig x <$> q a <*> b) f
  VLam f -> binder (\x b -> Lam x <$> b) f
  VId a x y -> Id <$> q a <*> q x <*> q y
  VRefl a -> Refl <$> q a
  VCon c as -> Con c <$> mapM q as
  VPair a b -> Pair <$> q a <*> q b
  VFst a -> Fst <$> q a
  VSnd a -> Snd <$> q a
  VProj a l -> (\a' -> Proj a' l) <$> q a
  -- a variable bound to its eta-expansion: only if the instance IS that
  -- variable's value (new R[r.x, c, d] is not r, though r.x is a field)
  VNamedE _ _ a -> q a
  VInst m r -> case [ x | (w, x) <- scEtas sc, eqVal w v0 ] of
    (x : _) -> Just (Var x)
    -- an element built with new: new M[args]
    [] -> do
      SegT me _ <- quoteWith sc (VSegT m [])
      as <- mapM (\p -> case lookupDyn r p of
                          VLvl l -> fmap ALv (qLvl l)
                          v      -> fmap ATm (q v)) (paramNames (modUnits m))
      Just (New (MApp me as))
  VSegT m fs -> do
    -- same segment means same id AND same dynamic part: ON.Side and
    -- OB.Side (ON = Outer[Nat], OB = Outer[Bool]) share the id
    let direct = case [ e | t <- scModsIx sc, (d, e) <- Map.findWithDefault [] (modId m) t, convs (scCC sc) d (modDyn m) ] of
          (e : _) -> Just e
          [] -> Nothing
    me <- case direct of
      Just me0 -> Just me0
      -- (instances in scope and their submodules are in scMods, checked
      -- by dynamic part above; paths through PARAMETERISED segments:)
      -- through segments with parameters: their values are in the
      -- segment's dynamic part (its dependencies include them)
      Nothing -> case [ MSub me0 (pname (last path)) | (j, path) <- scSegs sc, j == modId m, length path > 1
                         , Just ds <- [segDeps (init path) (pname (last path))]
                         , Just me0 <- [buildM (zip ds (modDyn m)) (init path) Nothing] ] of
          (me1 : _) -> Just me1
          [] -> Nothing
    fs' <- mapM (\(x, a) -> case a of
                    VLvl l -> fmap (\l' -> (x, ALv l')) (qLvl l)
                    _      -> fmap (\a' -> (x, ATm a')) (q a)) fs
    Just (SegT me fs')
  VLApp a l -> LApp <$> q a <*> qLvl l
  -- a sum or split reached by unfolding: the name of the definition it is
  -- the body of (the resolver names them so), if that name evaluates to it
  VSum t _ _ _   -> byTag t
  VSplit t _ _ _ -> byTag t
  _ -> Nothing
 where
  q = quoteWith sc
  k = scK sc
  binder mk f = let x = "h%" ++ show k
                    sc' = sc { scGens = (k, x) : scGens sc, scK = k + 1 }
                in mk x (quoteWith sc' (capp f (VGen k)))
  qLvl l = fmap (foldr1 LMax) (mapM atom (latoms l))
  atom (n, j) = fmap (\b -> iterate LSuc b !! j)
                     (if n == "0" then Just LZero else fmap LV (lookup n (scLvls sc)))
  -- a member of a segment with parameters, M[args].y: the arguments are
  -- the values the member's dynamic part records for M's parameters
  -- the values for the segment parameters: the dynamic part (paired with
  -- the dependency names) and the enclosing parameters the value carries
  viaSeg m path i d encl = case [ (y, ds) | UDef j y _ _ ds <- lastUnits path, j == i, m ++ "." ++ y == i ] of
    ((y, ds) : _) -> do
      let vals = zip (fst (splitDeps ds)) d ++ encl
      me <- buildM vals path Nothing
      Just (Acc me y)
    _ -> Nothing
  lastUnits path = case last path of (_, us, _) -> us
  -- the dependency names of submodule y of the last segment of a path
  segDeps path y = case [ ds | UMod _ y' _ ds <- lastUnits path, y' == y ] of
    (ds : _) -> Just ds
    [] -> Nothing
  buildM _ [] acc = acc
  buildM vals ((x, us, inst) : rest) acc = do
    let base = maybe (MVar x) (\m0 -> MSub m0 x) acc
    -- an instance already in scope is usable only if its arguments ARE the
    -- value's: otherwise it is another instance of the same segment
    instOk <- case inst of
      Just r -> if and [ conv (scCC sc) (lookupDyn r pn) v | pn <- paramNames us
                                                          , Just v <- [lookup pn vals] ]
                  then Just True else Nothing
      Nothing -> Just False
    me <- if not instOk && hasParams us
            then do as <- mapM (\pn -> do v <- lookup pn vals
                                          case v of
                                            VLvl l -> fmap ALv (qLvl l)
                                            _      -> fmap ATm (q v)) (paramNames us)
                    Just (MApp base as)
            else Just base
    buildM vals rest (Just me)
  byTag t = case [ h | (j, _, h) <- scDefs sc, j == t
                     , conv (scCC sc) (eval (scEnv sc) h) v0 ] of
    (h : _) -> Just h
    [] -> Nothing
  -- the names of the original text mean here what they meant there
  freeHere ns r = and [ sameName n r | n <- ns ]
  sameName n r = case (lookupAnyE r n, lookupAnyE (scEnv sc) n) of
    (Just (Left v), Just (Left w)) -> conv (scCC sc) v w
    (Just (Right m), Just (Right m')) -> modId m == modId m' && convs (scCC sc) (modDyn m) (modDyn m')
    (Nothing, Nothing) -> True
    _ -> False
  qSpine h [] = Just h
  qSpine h (el : rest) = do
    h' <- case el of
      EApp a  -> App h <$> q a
      EFst    -> Just (Fst h)
      ESnd    -> Just (Snd h)
      EProj l -> Just (Proj h l)
      ELApp l -> LApp h <$> qLvl l
    qSpine h' rest
