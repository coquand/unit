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
--        record R (..) {..} a record type: fields, new, split; never a module
--    Checking threads a context of units (final.pdf, chapter 3, generalised
--    to levels and constraints), and the environment is built from it.
--
--  * SEGMENTS SHARE.  An instance  M[args]  only binds M's parameters in an
--    environment.  A member  f  keeps ONE identity -- its qualified name --
--    and its value is the closure < f ; eta >: the unit and the environment
--    of its group.  Two occurrences of  M[fe,ua].f  are compared by name and
--    the dynamic part of that environment (ALL its variables and levels,
--    not only those f uses) before anything is unfolded.  This is
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

-- A module is a list of units with parameters (its body-less units, head
-- and body), used through instances; never a type.  A record has head
-- parameters (given at formation) and fields (its body-less body units);
-- it is a type, with the constructor  new  and an eliminator.
data SegKind = SModule | SRecord [Name]     -- a record: its head parameters
  deriving (Eq, Show)

data Unit
  = UDef  Id Name Exp Exp            -- id, name, type, body
  | UPar  Id Name Exp                -- a parameter / primitive notion
  | ULvl  Name                       -- a level variable
  | UCstr [Cs]                       -- constraints
  | UMod  Id Name SegKind [Unit]     -- a module or a record
  | UInst Id Name MExp               -- module N = M[args]
  | ULock [Id]                       -- the lock strategy from here on
  | UDir  Directive
  deriving (Eq, Show)

unitIdOf :: Unit -> Id
unitIdOf u = case u of
  UDef i _ _ _ -> i
  UMod i _ _ _ -> i
  UInst i _ _    -> i
  UPar i _ _     -> i
  _              -> ""

unitName :: Unit -> Name
unitName u = case u of
  UDef _ x _ _ -> x
  UPar _ x _     -> x
  ULvl x         -> x
  UMod _ x _ _ -> x
  UInst _ x _    -> x
  _              -> ""

-- The DYNAMIC part of an access to a definition (bengt.pdf slides 31-33)
-- is the values of all the variables and levels of its environment (dynOf),
-- not only those it uses: two accesses with the same unit are equal when
-- these are equal; a locked definition is otherwise never unfolded, so an
-- unused variable can tell two locked accesses apart (locks.seg, byDeps).

data Exp
  = U Lv
  | Var Name
  | App Exp Exp
  | Lam Name Exp
  | Pi Name Exp Exp
  | Let [Unit] Exp
  | Sum Id [(Name, Tel)]                     -- d_L (its occurrence), labels
  | Con Name [Exp]
  | Split Id [(Name, ([Name], [RecR], Exp))]  -- f_B (its occurrence), branches: the
                                             -- pattern variables, the recursive results
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
  | ProjU Exp Name                           -- e.l before the filling pass, which
                                             -- writes a fixed field as its value,
                                             -- a derived member as Mem, and
                                             -- otherwise a projection (below)
  | Mem MExp [Arg] Name Exp                  -- R[ps].d at the element e: the
                                             -- derived member d (filling pass)
  | Named Id Exp                             -- a sig occurrence with its
                                             -- internal name
  | Hole                                     -- a hidden argument, filled
                                             -- before the core sees the term
  | Unfilled                                 -- a hole whose filling failed
  deriving (Eq, Show)

-- The recursive results of a branch (PRIMREC.md): for the field at
-- position j, with n binders when it is a function field, the result
-- named y.  The resolver gives the names (position -1); the filling pass
-- gives the positions, from the data type, and evaluation reads only them.
data RecR = RecR Int Int Name
  deriving (Eq, Show)

recNames :: [RecR] -> [Name]
recNames rs = [ y | RecR _ _ y <- rs ]

-- the shape of a field of the data type d: Just n when it is recursive,
-- d ps or (ys : Psi) -> d ps with n binders (certified by Term.positivity)
recShape :: Id -> Exp -> Maybe Int
recShape d t = case t of
  Pi _ _ b -> fmap (+ 1) (recShape d b)
  _ -> case headE t of
         Var i | i == d -> Just 0
         _ -> Nothing
 where headE e = case e of { App a _ -> headE a; LApp a _ -> headE a; _ -> e }

-- the data definition of a sum (its occurrence is named after it)
sumDef :: Id -> Id
sumDef = takeWhile (/= '\0')

-- internal names, with the code identity of the split, constructor and
-- field (eqClos takes a binder name for its code)
recSelf :: Id -> Name -> Int -> Name
recSelf t c j = "%rec" ++ show j ++ "\1" ++ t ++ "/" ++ c

recArg :: Id -> Name -> Int -> Int -> Name
recArg t c j i = "%y" ++ show i ++ "\1" ++ t ++ "/" ++ c ++ "/" ++ show j

-- the binders of the TYPE of that result (distinct from the lambda's)
recTyArg :: Id -> Name -> Int -> Int -> Name
recTyArg t c j i = "%z" ++ show i ++ "\1" ++ t ++ "/" ++ c ++ "/" ++ show j

recMot :: Id -> Name -> Int -> Name
recMot t c j = "%mot" ++ show j ++ "\1" ++ t ++ "/" ++ c

recFld :: Id -> Name -> Int -> Name
recFld t c j = "%fld" ++ show j ++ "\1" ++ t ++ "/" ++ c

-- the recursive result for a function field x with n binders:
-- \ y1 .. yn -> self (x y1 .. yn)
recLam :: Id -> Name -> Int -> Int -> Name -> Exp
recLam t c j n x = foldr Lam (App (Var (recSelf t c j)) (foldl App (Var x) (map Var ys))) ys
 where ys = [ recArg t c j i | i <- [1 .. n] ]

-- the type of that result: (ys : Psi) -> mot (x ys), from the field type
-- (ys : Psi) -> d ps, its binders renamed
recTyExp :: Id -> Name -> Int -> Exp -> Exp
recTyExp t c j ft = go 1 [] ft
 where
  go i ren e = case e of
    Pi z a b -> let y = recTyArg t c j i
                in Pi y (renameVars ren a) (go (i + 1) ((z, y) : ren) b)
    _ -> App (Var (recMot t c j)) (foldl App (Var (recFld t c j)) [ Var y | (_, y) <- reverse ren ])

-- the holes of a term whose filling failed: Unfilled (an error when used),
-- so that they make no equalities in a run that trusts that definition
unfilledHoles :: Exp -> Exp
unfilledHoles e = case e of
  Hole -> Unfilled
  App a b -> App (go a) (go b); Lam x b -> Lam x (go b); Pi x a b -> Pi x (go a) (go b)
  Let us b -> Let (map unit us) (go b)
  Sum i cs -> Sum i [ (c, [ (x, go a) | (x, a) <- tel ]) | (c, tel) <- cs ]
  Con c as -> Con c (map go as)
  Split i bs -> Split i [ (c, (xs, rs, go b)) | (c, (xs, rs, b)) <- bs ]
  Sig x a b -> Sig x (go a) (go b); Pair a b -> Pair (go a) (go b); Fst a -> Fst (go a); Snd a -> Snd (go a)
  Rec t -> Rec [ (l, go a) | (l, a) <- t ]; Struct fs -> Struct [ (l, go a) | (l, a) <- fs ]
  Proj a l -> Proj (go a) l; ProjU a l -> ProjU (go a) l
  Id a x y -> Id (go a) (go x) (go y); Refl a -> Refl (go a)
  IdJ a x c d y p -> IdJ (go a) (go x) (go c) (go d) (go y) (go p)
  LPi x a -> LPi x (go a); LLam x a -> LLam x (go a); LApp a l -> LApp (go a) l; CPi cs a -> CPi cs (go a)
  Acc m x -> Acc (unfilledM m) x
  SegT m fs -> SegT (unfilledM m) [ (x, arg a) | (x, a) <- fs ]
  New m -> New (unfilledM m)
  Mem m as x a -> Mem (unfilledM m) (map arg as) x (go a)
  Named i a -> Named i (go a)
  _ -> e
 where
  go = unfilledHoles
  arg a = case a of { ATm x -> ATm (go x); _ -> a }
  unit u = case u of { UDef i x a b -> UDef i x (go a) (go b); _ -> u }

unfilledM :: MExp -> MExp
unfilledM m = case m of
  MVar _ -> m
  MSub n x -> MSub (unfilledM n) x
  MApp n as -> MApp (unfilledM n) [ case a of { ATm x -> ATm (unfilledHoles x); _ -> a } | a <- as ]

-- rename free variables (the binders of the program are unique, so no
-- capture: Wang's no-shadowing rule)
renameVars :: [(Name, Name)] -> Exp -> Exp
renameVars [] e = e
renameVars ren e = case e of
  Var x -> Var (fromMaybe x (lookup x ren))
  App a b -> App (go a) (go b); Lam x b -> Lam x (go b); Pi x a b -> Pi x (go a) (go b)
  Let us b -> Let (map unit us) (go b)
  Sum i cs -> Sum i [ (c, [ (x, go a) | (x, a) <- tel ]) | (c, tel) <- cs ]
  Con c as -> Con c (map go as)
  Split i bs -> Split i [ (c, (xs, rs, go b)) | (c, (xs, rs, b)) <- bs ]
  Sig x a b -> Sig x (go a) (go b); Pair a b -> Pair (go a) (go b); Fst a -> Fst (go a); Snd a -> Snd (go a)
  Rec t -> Rec [ (l, go a) | (l, a) <- t ]; Struct fs -> Struct [ (l, go a) | (l, a) <- fs ]
  Proj a l -> Proj (go a) l; ProjU a l -> ProjU (go a) l
  Id a x y -> Id (go a) (go x) (go y); Refl a -> Refl (go a)
  IdJ a x c d y p -> IdJ (go a) (go x) (go c) (go d) (go y) (go p)
  LPi x a -> LPi x (go a); LLam x a -> LLam x (go a); LApp a l -> LApp (go a) l; CPi cs a -> CPi cs (go a)
  Acc m x -> Acc (mexp m) x
  SegT m fs -> SegT (mexp m) [ (x, arg a) | (x, a) <- fs ]
  New m -> New (mexp m)
  Mem m as x a -> Mem (mexp m) (map arg as) x (go a)
  Named i a -> Named i (go a)
  _ -> e
 where
  go = renameVars ren
  arg a = case a of { ATm x -> ATm (go x); _ -> a }
  mexp m = case m of { MVar _ -> m; MSub n x -> MSub (mexp n) x; MApp n as -> MApp (mexp n) (map arg as) }
  unit u = case u of { UDef i x a b -> UDef i x (go a) (go b); _ -> u }

------------------------------------------------------------------------
-- 2.  Values

data Env
  = ENil
  | EVar Env Name Val
  | EDecl Env Name Val                      -- a declared variable of segment
                                            -- type: itself with the fields its
                                            -- type fixes (never dynamic)
  | ELvl Env Name Lvl
  | EDef Env [Unit] [(Name, Ent)] QFrag     -- a mutual group, evaluated once,
                                           -- with its part of the naming
                                           -- table (for quoting), built once

data Ent = EVal Val | EMod Mod

-- a segment: its units, the environment where it is declared, its
-- identity (id and the values of what it depends on), and, once all its
-- parameters are given, the instance environment
data Mod = Mod { modId :: Id, modDyn :: [Val], modUnits :: [Unit], modEnv :: Env
               , modInst :: Maybe Env, modKind :: SegKind }

data Clos  = Clos Name Exp Env
data LClos = LClos Name Exp Env

data Elim = EApp Val | EFst | ESnd | EProj Name | ELApp Lvl

-- Sigma and record types are compared BY NAME (Half, Cederquist 7.1;
-- Gofer's is_intensional): the internal name of the occurrence, the names
-- and the values of the variables it depends on.  Never by their fields.
type SName = Maybe (Id, [Val])

data Val
  = VU Lvl
  | VGen Int                                -- a generic variable
  | VConst Id [Val]                         -- a rigid constant (parameter, PN)
  | VRef Unit Env                           -- the closure < f ; eta > of an
                                            -- access to a definition: the unit
                                            -- as written and the environment
                                            -- of its group.  Nothing else: its
                                            -- body is evaluated when the head
                                            -- is needed, under the lock
  | VVar Name Mod [(Name, Val)]             -- a variable of record type: itself, with
                                            -- its record and the head parameters its
                                            -- type gives (for its derived members);
                                            -- a fixed field is NOT a value here (§4:
                                            -- it is elaborated where t.x is checked)
                                            -- (was: a declared variable of record type:
                                            -- itself, with the fields its type
                                            -- fixes ( c : M[x := e]  gives
                                            -- c.x = e )
  | VLvl Lvl                                -- a level, inside dynamic parts
  | VApp Val Val
  | VLam Clos
  | VPi Val Clos
  | VCon Name [Val]
  | VSum Id [Val] [(Name, Tel)] Env
  | VSplit Id [Val] [(Name, ([Name], [RecR], Exp))] Env
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
  | VInst Mod Env                           -- an element  new R[..] : the record
                                            -- and the environment of its
                                            -- parameters and fields

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
  Sum t cs   -> VSum t (dynVals r) cs r
  Con c as     -> VCon c (map (eval r) as)
  Split t bs -> VSplit t (dynVals r) bs r
  Sig x a b    -> VSig Nothing (eval r a) (Clos x b r)
  Pair a b     -> VPair (eval r a) (eval r b)
  Fst a        -> vfst (eval r a)
  Snd a        -> vsnd (eval r a)
  Rec tel      -> VRec Nothing tel r
  Named i e    -> let d  = dynVals r
                      nm = Just (i, d)
                  in case eval r e of
                       VSig _ a f  -> VSig nm a f
                       VRec _ t r' -> VRec nm t r'
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
  Acc m x      -> lookupMember (instOf (evalMod r m)) x
  SegT m fs    -> VSegT (evalMod r m) [ (x, evalArg r a) | (x, a) <- fs ]
  New m        -> let md = evalMod r m in VInst md (instOf md)
  ProjU a l    -> vproj (eval r a) l
  Mem m as l a -> let md = evalMod r m
                  in memberAt md (zip (paramNames (headUnits md)) (map (evalArg r) as)) (eval r a) l
  -- a placeholder while the filling pass works on a term (it evaluates
  -- partly filled terms); a filled term has no hole
  Hole         -> VConst "_unfilled" []
  -- a hole left by a failed filling pass (unfilledHoles): never equal to
  -- anything, an error when used
  Unfilled     -> error "a hidden argument was not filled (its definition failed)"

capp :: Clos -> Val -> Val
capp (Clos x b r) v = eval (EVar r x v) b

lcapp :: LClos -> Lvl -> Val
lcapp (LClos x b r) l = eval (ELvl r x l) b

-- Elimination.  An access to a definition is a closure < f ; eta >; an
-- elimination of it is an ordinary neutral form, until whnf computes the
-- head.  A split whose argument is not yet a constructor is stuck, and
-- whnf resumes it.  eval never consults the lock.
app :: Val -> Val -> Val
app (VLam f) v = capp f v
app f@(VSplit t _ bs r) v = case v of
  VCon c vs -> case lookup c bs of
    Just (xs, rs, b) -> eval (recBind t c f (bindAll r xs vs) xs vs rs) b
    Nothing      -> error ("split: no branch for " ++ c)
  -- a record: the branch applied to its fields (beta for the eliminator)
  _ | Just vs <- recordFields v, [(_, (xs, _, b))] <- bs -> eval (bindAll r xs vs) b
  _ -> VApp f v
app u v = VApp u v

-- the recursive results of a branch (PRIMREC.md 5.2): the split itself
-- applied to the recursive fields, at the positions the filling pass
-- certified; lazy
recBind :: Id -> Name -> Val -> Env -> [Name] -> [Val] -> [RecR] -> Env
recBind t c f r0 xs vs = foldl bindRec r0
 where
  bindRec r (RecR j n y)
    -- not annotated: the definition did not pass the filling pass (it is
    -- reported there); its results are never equal to anything (lazy)
    | j < 0     = EVar r y (error ("recursive result " ++ shortName y ++ " of " ++ shortId t
                                   ++ ": the split was not annotated (its definition failed)"))
    | n == 0    = EVar r y (app f (vs !! j))
    | otherwise = EVar r y (eval (EVar r0 (recSelf t c j) f) (recLam t c j n (xs !! j)))

vfst :: Val -> Val
vfst (VPair u _)       = u
vfst w                 = VFst w

vsnd :: Val -> Val
vsnd (VPair _ v)       = v
vsnd w                 = VSnd w

vproj :: Val -> Name -> Val
vproj (VStruct fs) l     = fromMaybe (error ("no field " ++ l)) (lookup l fs)
vproj w@(VVar _ md fs) l
  | isDerived md l       = memberAt md fs w l
  | otherwise            = VProj w l
vproj w@(VInst m r) l
  | isDerived m l        = memberAt m [ (h, lookupDyn r h) | h <- recordHeads m ] w l
  | otherwise            = lookupMember r l
vproj w l                = VProj w l

lapp :: Val -> Lvl -> Val
lapp (VLLam f) l        = lcapp f l
lapp w l                = VLApp w l

vidj :: Val -> Val -> Val -> Val -> Val -> Val -> Val
vidj _ _ _ d _ (VRefl _) = d
vidj a x c d y p         = VIdJ a x c d y p

-- the fields of a constructed record (not its head parameters, which its
-- type gives), or the fields of a struct
recordFields :: Val -> Maybe [Val]
recordFields v = case v of
  VInst m r   -> Just [ lookupDyn r p | p <- recordFieldNames m ]
  VStruct fs  -> Just (map snd fs)
  _           -> Nothing

bindAll :: Env -> [Name] -> [Val] -> Env
bindAll r []       []       = r
bindAll r (x : xs) (v : vs) = bindAll (EVar r x v) xs vs
bindAll _ _        _        = error "split: constructor arity mismatch"

-- a mutual group of definitions, modules and instances (mTT10's D rho).
-- The definitions stay as written: nothing is evaluated, an access finds
-- the unit (lookupVal).  Segments and instances are entered once.
mkGroup :: Env -> [Unit] -> Env
mkGroup r us = rho
 where
  ents = concatMap entry us
  rho = EDef r us ents (fragOf rho us ents)
  entry u = case u of
    UDef _ x _ _  -> [(x, EVal (mkRef u rho))]
    UMod i x k mus -> [(x, EMod (Mod i (dynVals rho) mus rho
                                   (if hasParams mus then Nothing
                                    else Just (instUnits rho mus [])) k))]
    UInst _ x m     -> [(x, EMod (evalMod rho m))]
    _               -> []

defId :: Unit -> Id
defId (UDef i _ _ _) = i
defId _                = ""

-- the dynamic part of an environment: the values of its variables and
-- levels, innermost first; the definition groups are static (R(D rho) =
-- R rho)
-- every variable binding (for writing a member back as M[args].f)
allBound :: Env -> [(Name, Val)]
allBound r = case r of
  ENil           -> []
  EVar r' x v    -> (x, v) : allBound r'
  EDecl r' x v   -> (x, v) : allBound r'
  ELvl r' x l    -> (x, VLvl l) : allBound r'
  EDef r' _ _ _  -> allBound r'

dynOf :: Env -> [(Name, Val)]
dynOf r = case r of
  ENil           -> []
  EVar r' x v    -> (x, v) : dynOf r'
  EDecl r' _ _   -> dynOf r'
  ELvl r' x l    -> (x, VLvl l) : dynOf r'
  EDef _ _ _ fr  -> fDyn fr          -- computed once per frame

dynVals :: Env -> [Val]
dynVals = map snd . dynOf

-- an access to a definition, with its evaluated body (lazily)
mkRef :: Unit -> Env -> Val
mkRef = VRef

-- the body of a definition, evaluated in its environment
unfoldRef :: Unit -> Env -> Val
unfoldRef (UDef _ _ _ b) r = eval r b
unfoldRef _ _                = error "unfoldRef: not a definition"

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
  go ENil = VConst x []                  -- a declared variable: itself
  go (EVar r y v) = if x == y then v else go r
  go (EDecl r y v) = if x == y then v else go r
  go (ELvl r y _) = if x == y then error ("level used as a term: " ++ x) else go r
  -- a definition is found by its id (the resolver writes every access
  -- to a definition as its id): the closure < f ; eta >
  go (EDef r _ _ fr) = case Map.lookup x (fIndex fr) of
      Just (EVal v) -> v
      Just (EMod _) -> go r      -- a segment is not a term: a declared variable of that name
      Nothing       -> go r

-- a member of an instance, by its name in the segment
lookupMember :: Env -> Name -> Val
lookupMember r0 x = go r0
 where
  go ENil = error ("no member: " ++ x)
  go (EVar r y v) = if x == y then v else go r
  go (EDecl r y v) = if x == y then v else go r
  go (ELvl r y _) = if x == y then error ("level used as a term: " ++ x) else go r
  go (EDef r _ es _) = case () of
    _ -> case lookup x es of
      Just (EVal v) -> v
      Just (EMod _) -> error ("module used as a term: " ++ x)
      Nothing       -> go r

lookupLvl :: Env -> Name -> Lvl
lookupLvl r0 x = go r0
 where
  go ENil = lvar x
  go (EVar r _ _) = go r
  go (EDecl r _ _) = go r
  go (ELvl r y l) = if x == y then l else go r
  go (EDef r _ _ _) = go r

lookupMod :: Env -> Name -> Mod
lookupMod r0 x = go r0
 where
  go ENil = error ("unbound module: " ++ x)
  go (EVar r _ _) = go r
  go (EDecl r _ _) = go r
  go (ELvl r _ _) = go r
  go (EDef r _ _ fr) = case Map.lookup x (fIndex fr) of
    Just (EMod m) -> m
    Just _        -> error ("not a module: " ++ x)
    Nothing       -> go r

-- the value of a dependency: a variable or a level
lookupDyn :: Env -> Name -> Val
lookupDyn r0 x = go r0
 where
  go ENil = VConst x []
  go (EVar r y v) = if x == y then v else go r
  go (EDecl r y v) = if x == y then v else go r
  go (ELvl r y l) = if x == y then VLvl l else go r
  go (EDef r _ _ _) = go r

-- the fields of a record: its body-less units that are not head parameters
recordFieldNames :: Mod -> [Name]
recordFieldNames md = case modKind md of
  SRecord hs -> [ x | x <- termParams (modUnits md), x `notElem` hs ]
  SModule    -> []

-- the units of a record's head (its parameters and their constraints)
headUnits :: Mod -> [Unit]
headUnits md = [ u | u <- modUnits md, isHead u ]
 where hs = recordHeads md
       isHead u = case u of
         UPar _ p _ -> p `elem` hs
         ULvl p     -> p `elem` hs
         _          -> False

-- the head parameters of a record
recordHeads :: Mod -> [Name]
recordHeads md = case modKind md of
  SRecord hs -> hs
  SModule    -> []

-- a derived member of a record: a definition of its body
isDerived :: Mod -> Name -> Bool
isDerived md l = case (modKind md, memberUnit (modUnits md) l) of
  (SRecord _, Just (UDef{})) -> True
  _                          -> False

-- The environment of the derived members of a record at the element t:
-- the head parameters (dynamic), then the element itself (dynamic, as
-- %self), then the fields as t.x (static: determined by t).  A derived
-- member  t.d  is the access to d there, so it is  R.d[ps] t : compared by
-- d, ps and t (never by t's fields), and unfolded under the lock strategy.
selfEnv :: Mod -> [(Name, Val)] -> Val -> Env
selfEnv md heads t = selfEnvFixed md heads [] t

-- the same, with the fields a type fixes bound to their values: only for
-- computing TYPES (of derived members at  t : R[ps][x := e] ), never values,
-- so that fixed fields never enter equality (RECORDS.md §4)
selfEnvFixed :: Mod -> [(Name, Val)] -> [(Name, Val)] -> Val -> Env
selfEnvFixed md heads fixed t = go (modEnv md) False (modUnits md)
 where
  hs = recordHeads md
  go r _ [] = r
  go r self (u : us) = case u of
    UPar _ p _ | p `elem` hs -> go (EVar r p (headVal p)) self us
    ULvl p | VLvl l <- headVal p -> go (ELvl r p l) self us
    UCstr _ -> go r self us
    _ | not self -> go (EVar r "%self" t) True (u : us)
    UPar _ p _ -> go (EDecl r p (fromMaybe (vproj t p) (lookup p fixed))) self us
    UDef{} -> let (g, rest) = span isGroupUnit (u : us) in go (mkGroup r g) self rest
    -- an open of a module instance: its arguments see the fields as t.x
    UInst{} -> go (mkGroup r [u]) self us
    _ -> go r self us
  headVal p = fromMaybe (VConst p []) (lookup p heads)

memberAt :: Mod -> [(Name, Val)] -> Val -> Name -> Val
memberAt md heads t l = lookupMember (selfEnv md heads t) l

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

-- how often the conversion of splits falls back to their branches
fallbackCount :: IORef Int
fallbackCount = unsafePerformIO (newIORef 0)
{-# NOINLINE fallbackCount #-}

countFallback :: Bool -> Bool
countFallback b = unsafePerformIO (modifyIORef' fallbackCount (+ 1) >> return b)
{-# NOINLINE countFallback #-}
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


whnf :: Locks -> Val -> Val
whnf s = whnfP (`Set.notMember` s)

-- weak head normal form without unfolding any definition: only beta,
-- projections, splits on constructors and idJ on refl (the folded view)
whnfFolded :: Val -> Val
whnfFolded = whnfP (const False)

-- weak head normal form, unfolding the definitions that u selects
whnfP :: (Id -> Bool) -> Val -> Val
whnfP u v = case v of
  VRef r e | u (defId r) -> countUnfold (defId r) (whnfP u (unfoldRef r e))
  VApp f a -> case whnfP u f of
    f'@(VSplit{}) -> case whnfP u a of
      a'@(VCon _ _) -> whnfP u (app f' a')
      a' | Just _ <- recordFields a' -> whnfP u (app f' a')
         | otherwise -> VApp f' a'
    VLam cl -> whnfP u (capp cl a)
    f' -> VApp f' a                      -- a locked head stays
  VFst p -> case whnfP u p of
    VPair a _ -> whnfP u a
    p'        -> vfst p'
  VSnd p -> case whnfP u p of
    VPair _ b -> whnfP u b
    p'        -> vsnd p'
  VProj p l -> case whnfP u p of
    VStruct fs -> whnfP u (fromMaybe (error ("no field " ++ l)) (lookup l fs))
    i@(VInst _ _) -> whnfP u (vproj i l)
    w@(VVar{}) -> case vproj w l of
                    VProj{} -> VProj w l
                    a       -> whnfP u a
    p'         -> vproj p' l
  VLApp t l -> case whnfP u t of
    VLLam cl -> whnfP u (lcapp cl l)
    t'       -> VLApp t' l
  VIdJ a x c d y p -> case whnfP u p of
    VRefl _ -> whnfP u d
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
  | sameDef u v     = True                  -- lazy delta: the same definition at convertible arguments
  | otherwise       = traceConv u v (conv' c (whnf (ccS c) u) (whnf (ccS c) v))
 where
  -- two eliminations of accesses to the same definition, in environments
  -- with convertible dynamic parts, are equal when their arguments are;
  -- otherwise both heads are computed
  sameDef a b = case (spineE a [], spineE b []) of
    ((VRef u1 r1, e1), (VRef u2 r2, e2)) | d1 <- dynVals r1, d2 <- dynVals r2 ->
      defId u1 == defId u2 && length e1 == length e2
      && convs c d1 d2 && convSp c e1 e2
    _ -> False
  spineE v es = case v of
    VApp f a  -> spineE f (EApp a : es)
    VFst p    -> spineE p (EFst : es)
    VSnd p    -> spineE p (ESnd : es)
    VProj p l -> spineE p (EProj l : es)
    VLApp p l -> spineE p (ELApp l : es)
    _         -> (v, es)

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
  (VVar x _ _, VVar y _ _)         -> x == y
  (VRef u r, VRef u' r')           -> defId u == defId u' && eqEnvs r r'
  (VApp a b, VApp a' b')           -> eqVal a a' && eqVal b b'
  (VLam f, VLam g)                 -> eqClos f g
  (VPi a f, VPi b g)               -> eqVal a b && eqClos f g
  (VSig (Just (i, d)) _ _, VSig (Just (j, e)) _ _) -> i == j && eqVals d e
  (VSig _ a f, VSig _ b g)         -> eqVal a b && eqClos f g
  (VRec (Just (i, d)) _ _, VRec (Just (j, e)) _ _) -> i == j && eqVals d e
  (VCon c as, VCon d bs)           -> c == d && eqVals as bs
  (VSum t d _ _, VSum t' d' _ _)   -> t == t' && eqVals d d'
  (VSplit t d _ _, VSplit t' d' _ _) -> t == t' && eqVals d d'
  (VPair a b, VPair a' b')         -> eqVal a a' && eqVal b b'
  (VFst a, VFst b)                 -> eqVal a b
  (VSnd a, VSnd b)                 -> eqVal a b
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
  (VInst m r, VInst n r')          -> modId m == modId n
                                      && and [ eqVal (lookupDyn r x) (lookupDyn r' x) | x <- paramNames (modUnits m) ]
  _                                -> False

eqVals :: [Val] -> [Val] -> Bool
eqVals [] [] = True
eqVals (a : as) (b : bs) = eqVal a b && eqVals as bs
eqVals _ _ = False

-- the dynamic parts of two environments: the same variables with equal
-- values
eqEnvs :: Env -> Env -> Bool
eqEnvs r s = go (dynOf r) (dynOf s)
 where
  go [] [] = True
  go ((x, v) : vs) ((y, w) : ws) = x == y && eqVal v w && go vs ws
  go _ _ = False

-- a binder with a code identity (SegParse.binderUnits): the same binder is
-- the same occurrence of code, hence the same body
hasCodeId :: Name -> Bool
hasCodeId = elem '\1'

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
eqClos (Clos x _ r) (Clos y _ r') = x == y && hasCodeId x && eqEnvs r r'   -- the same occurrence

eqLClos :: LClos -> LClos -> Bool
eqLClos (LClos x _ r) (LClos y _ r') = x == y && hasCodeId x && eqEnvs r r'

conv' :: CC -> Val -> Val -> Bool
conv' c u1 u2 = case (u1, u2) of
  (VRef u1 r1, VRef u2 r2) -> defId u1 == defId u2 && convs c (dynVals r1) (dynVals r2)
  (VU l, VU m)                 -> eqLvl th l m
  (VLvl l, VLvl m)             -> eqLvl th l m
  (VGen i, VGen j)             -> i == j
  (VConst i d1, VConst j d2)   -> i == j && convs c d1 d2
  (VVar x _ _, VVar y _ _)     -> x == y
  (VLam _, _)                  -> etaEq
  (_, VLam _)                  -> etaEq
  (VLLam _, _)                 -> letaEq
  (_, VLLam _)                 -> letaEq
  (VPair a b, VPair a' b')     -> conv c a a' && conv c b b'
  (VPair a b, w)               -> conv c a (vfst w) && conv c b (vsnd w)
  (w, VPair a b)               -> conv c (vfst w) a && conv c (vsnd w) b
  -- two elements built by new: the same record, convertible parameters
  -- and fields (new is the constructor; no eta)
  (VInst m1 r1, VInst m2 r2)   -> modId m1 == modId m2
                                  && and [ conv c (lookupDyn r1 x) (lookupDyn r2 x) | x <- paramNames (modUnits m1) ]
  (VSegT m1 f1, VSegT m2 f2)   -> modId m1 == modId m2 && convs c (modDyn m1) (modDyn m2)
                                  && map fst f1 == map fst f2
                                  && convs c (map snd f1) (map snd f2)
  (VStruct fs, VStruct gs)     -> map fst fs == map fst gs
                                  && and (zipWith (conv c) (map snd fs) (map snd gs))
  (VPi a f, VPi b g)           -> conv c a b && conv c' (capp f x) (capp g x)
  -- by name: the same occurrence and the same values of its dependencies
  -- records are nominal: the same occurrence with equal dynamic parts
  (VSig (Just (i, d1)) _ _, VSig (Just (j, d2)) _ _) -> i == j && convs c d1 d2
  (VRec (Just (i, d1)) _ _, VRec (Just (j, d2)) _ _) -> i == j && convs c d1 d2
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
  (VSum t1 d1 cs r1, VSum t2 d2 _ r2)    -> t1 == t2 && (convs c d1 d2 ||
      and [ convTel c tel r1 tel r2 | (_, tel) <- cs ])
  -- the same split: the same dynamic part, or else (EXPERIMENTAL,
  -- counted) the same branches under fresh variables for the pattern
  -- variables AND the recursive results (PRIMREC.md 5.3)
  (VSplit t1 d1 bs r1, VSplit t2 d2 _ r2) -> t1 == t2 && (convs c d1 d2 ||
      countFallback (and [ conv (c { ccK = k + length ys }) (eval (bindAll r1 ys gens) b) (eval (bindAll r2 ys gens) b)
          | (_, (xs, rs, b)) <- bs, let ys = xs ++ recNames rs
          , let gens = [ VGen (k + j) | j <- [0 .. length ys - 1] ] ]))
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
  VVar x _ _    -> Var (if take 2 x == "%v" then '#' : drop 2 x else x)
  -- a definition with its dynamic part: the values of the variables of its
  -- environment, outermost first (for a member of a segment: its parameters)
  VRef u r      -> Var (qualName (defId u) ++ dynB [ v | (x, v) <- reverse (dynOf r), not (ambient x v) ])
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
  -- the dynamic part, when there is one:  M.f{A := N, ..}
  dynS [] = ""
  dynS d  = "{" ++ commaSep (map (prettyAt 3 . go) d) ++ "}"
  dynB [] = ""
  dynB d  = "[" ++ commaSep (map (prettyAt 8 . go) d) ++ "]"
  -- a variable bound to itself (a parameter of the whole file): not shown
  ambient x v = case v of
    VLvl l    -> latoms l == [(x, 0)]
    VConst c [] -> c == x
    _         -> False
  rbTel _ [] _ = []
  rbTel j ((l, a) : tel) r = (l, rb full s j (eval r a)) : rbTel (j+1) tel (EVar r l (VGen j))


-- an application as its head and arguments
appSpine :: Val -> [Val] -> (Val, [Val])
appSpine v as = case v of
  VApp f a -> appSpine f (a : as)
  _        -> (v, as)

lvToLv :: Lvl -> Lv
lvToLv l = foldr1 LMax [ iterate LSuc (if x == "0" then LZero else LV x) !! n | (x, n) <- latoms l ]

csToCs :: Cstr -> Cs
csToCs c = case c of
  CEq l m -> Cs (lvToLv l) REq (lvToLv m)
  CLe l m -> Cs (lvToLv l) RLe (lvToLv m)
  CLt l m -> Cs (lvToLv l) RLt (lvToLv m)

-- the printed name: drop the occurrence tag
shortId :: Id -> String
shortId = takeWhile (`notElem` "#\0\1")

-- the printed name of a binder: without its code identity
binderName :: Name -> String
binderName = takeWhile (/= '\1')

-- the printed name of a definition with the segment it belongs to:  M.f
qualName :: Id -> String
qualName i = case reverse (splitOn (takeWhile (`notElem` "#\0") i)) of
  (f : m : _) | m /= "" && takeWhile (/= '/') f == f -> m ++ "." ++ f
  _ -> shortName i
 where splitOn str = case break (== '.') str of
         (a, _ : b) -> a : splitOn b
         (a, [])    -> [a]

-- the printed name of a definition: its own name, without its path
shortName :: Id -> String
shortName i = case i of
  '#' : _ -> i                         -- a generic variable  #k
  _ | '[' `elem` i -> i                -- printed with its dynamic part
  _ | length (filter (== '.') (shortId i)) <= 1, '/' `notElem` i -> shortId i   -- f or M.f
    | otherwise -> reverse (takeWhile (`notElem` "./") (reverse (shortId i)))

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
  go _ _ (Var x)     = shortName x
  go _ _ (Sum t _) = shortId t
  go _ _ (Split t _) = shortId t
  go d n (App a b)   = paren (d > 10) (pr 10 n a ++ " " ++ pr 11 (n-1) b)
  go d n (LApp a l)  = paren (d > 10) (pr 10 n a ++ " @" ++ plv True l)
  go d n (Lam x b)   = paren (d > 0) ("\\ " ++ binderName x ++ " -> " ++ pr 0 (n-1) b)
  go d n (LLam x b)  = paren (d > 0) ("<" ++ binderName x ++ "> " ++ pr 0 (n-1) b)
  go d n (LPi x b)   = paren (d > 1) ("[" ++ binderName x ++ "] " ++ pr 1 (n-1) b)
  go d n (CPi cs b)  = paren (d > 1) ("[" ++ commaSep (map pcs cs) ++ "] " ++ pr 1 (n-1) b)
  go d n (Pi x a b)
    | x == "_"       = paren (d > 1) (pr 2 (n-1) a ++ " -> " ++ pr 1 (n-1) b)
    | otherwise      = paren (d > 1) ("(" ++ binderName x ++ " : " ++ pr 0 (n-1) a ++ ") -> " ++ pr 1 (n-1) b)
  go d n (Sig x a b)
    | x == "_"       = paren (d > 2) (pr 3 (n-1) a ++ " * " ++ pr 2 (n-1) b)
    | otherwise      = paren (d > 2) ("(" ++ binderName x ++ " : " ++ pr 0 (n-1) a ++ ") * " ++ pr 2 (n-1) b)
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
  go d n (Named _ a) = pr d n a
  go d n (ProjU a l)  = paren (d > 11) (pr 11 (n-1) a ++ "." ++ l)
  go d n (Mem _ _ l a) = paren (d > 11) (pr 11 (n-1) a ++ "." ++ l)
  paren True  t = "(" ++ t ++ ")"
  paren False t = t
  pm (MVar x)     = let y = reverse (takeWhile (`notElem` "./") (reverse x)) in if take 5 y == "open#" then "" else shortName x
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

-- A fresh variable of record type is itself (no eta for records), with
-- its record and the parameters its type gives, which its derived members
-- need.  A fixed field is not a value here: c.x is written as the fixed
-- value where it is checked (RECORDS.md §4).
etaV :: Val -> Val -> Val
etaV t v = case (whnf Set.empty t, v) of
  (VSegT md fs, VGen k) -> VVar (freshVarName k) md fs
  _ -> v

-- the name of the fresh variable k when it has a segment type
freshVarName :: Int -> Name
freshVarName k = "%v" ++ show k

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
  Named _ e' -> checkType cx e'
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
      -- the original pair, with no constant unfolded
      else failWith ("refl " ++ pretty a ++ " does not prove " ++ showV cx t0 ++
                     concat [ "\n  not convertible (no constant unfolded):  " ++ showV cx l ++ "   /=   " ++ showV cx r
                            | (l, r) <- [ (va, x) | not (conv (cc cx) va x) ] ++ [ (va, y) | not (conv (cc cx) va y) ] ])
  (Sum _ cs, VU _) -> mapM_ (\(_, tel) -> checkTelIn cx tel t) cs
  (Con c as, VSum _ _ cs r) -> case lookup c cs of
    Nothing  -> failWith ("constructor " ++ c ++ " is not in " ++ showV cx t)
    Just tel -> checkArgs cx as tel r
  (Split _ bs, VPi dom f) -> case force cx dom of
    VSum st _ cs r -> checkSplit cx st bs cs r f
    d -> case bs of
      -- a record: one branch binding its fields, checked at the canonical
      -- element built from them
      [(_, (_, _ : _, _))] -> failWith "split on a record: a record has no recursive results"
      [(_, (xs, _, b))] | Just (cx', el) <- recordBranch cx d xs -> check cx' b (capp f el)
      [(_, (xs, _, _))] | VSegT md _ <- d, SRecord _ <- modKind md ->
        failWith ("the pattern binds " ++ show (length xs) ++ " variables; the fields of "
                  ++ showV cx d ++ " are " ++ unwords (recordFieldNames md)
                  ++ " (its parameters are given by the type)")
      _ -> failWith ("split on a non-sum type " ++ showV cx d)
  (Named _ e', _) -> check cx e' t0
  (Let us b, _) -> do cx' <- checkLocal cx us
                      check cx' b t
  _ -> do
    t' <- inferD cx e
    if sub cx t' t || subSeg t' then ok
      -- the original pair, with no constant unfolded
      else failWith ("type mismatch for  " ++ pretty e ++
                     "\n  expected : " ++ showV cx t0 ++
                     "\n  inferred : " ++ showV cx t' ++
                     "\n  (no constant unfolded; they are not convertible)")
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
      VSegT md fs | isDerived md l, Just (UDef _ _ ty _) <- memberUnit (modUnits md) l ->
        Right (eval (selfEnvFixed md fs fs (ev cx a)) ty)
      VSegT md fs -> do
        let v = ev cx a
            r = case v of
              VInst _ r' -> r'
              _ -> instUnits (modEnv md) (modUnits md)
                     [ fromMaybe (vproj v p) (lookup p fs) | p <- paramNames (modUnits md) ]
        case memberUnit (modUnits md) l of
          Just (UDef _ _ ty _) -> Right (eval r ty)
          Just (UPar _ _ ty)     -> Right (eval r ty)
          _ -> failWith ("no member " ++ l ++ " in " ++ showV cx t)
      t' -> failWith ("not a record: " ++ pretty a ++ " : " ++ showV cx t')
  Named _ e' -> infer cx e'
  Mem _ _ l a -> infer cx (Proj a l)
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
    case modKind md of
      SModule -> failWith ("new " ++ showM m ++ ": a module; declare it with `record`")
      SRecord _ -> ok
    -- the type is  R[ps] , the head parameters only: a fixed field is read
    -- off the element's value where needed (subSeg), and a type that does
    -- not mention the fields can be a codomain (apH (\ c -> new M[.., c]))
    let r = instOf md
    Right (VSegT md [ (p, lookupDyn r p) | p <- paramNames (headUnits md) ])
  Acc m x -> do
    md <- checkMod cx m
    case memberUnit (modUnits md) x of
      Just (UDef _ _ a _) -> Right (eval (instOf md) a)
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
  case modKind md of
    SModule -> failWith (showM m ++ " is a module; declare it with `record` to use it as a type")
    SRecord hs -> case [ h | h <- hs, h `notElem` map fst fs ] of
      [] -> ok
      missing -> failWith ("the record " ++ showM m ++ " needs its parameters " ++ unwords missing)
  vs <- go (modEnv md) (modUnits md)
  Right (md, vs)
 where
  go _ [] = Right []
  go r (u : us) = case u of
    UPar i x a -> case lookup x fs of
      Just (ATm e) -> do
        -- the type of a fixed field may mention only fixed fields (and
        -- the head parameters, which are always given)
        case [ y | y <- freeNamesE a, VConst ('?' : _) [] <- [lookupDyn r y] ] of
          (y : _) -> failWith ("the field " ++ x ++ " of " ++ showM m ++ " can be fixed only if "
                               ++ y ++ " is fixed too: its type mentions " ++ y)
          [] -> ok
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

-- The branch of the eliminator of a record type: its binders are the
-- fields of the record (not its head parameters, which the type gives) or
-- the fields of the sig.  A field the type fixes (provisional, §4 of
-- RECORDS.md) is bound to its value.  The context with the binders, and
-- the canonical element built from them.
recordBranch :: Cx -> Val -> [Name] -> Maybe (Cx, Val)
recordBranch cx d xs = case d of
  VSegT md fs | SRecord _ <- modKind md
              , length xs == length (recordFieldNames md) -> go cx (modEnv md) (modUnits md) xs
   where
    hs = case modKind md of { SRecord h -> h; SModule -> [] }
    go c r [] [] = Just (c, VInst md r)
    go c r (u : us) ys = case (u, ys) of
      (UPar _ p _, _) | p `elem` hs -> case lookup p fs of
        Just v  -> go c (EVar r p v) us ys
        Nothing -> Nothing
      (UPar _ p a, y : ys') -> case lookup p fs of
        Just v  -> go (c { cxEnv = EVar (cxEnv c) y v, cxTys = (y, eval r a) : cxTys c }) (EVar r p v) us ys'
        Nothing -> let (c', g) = extVar c y (eval r a) in go c' (EVar r p g) us ys'
      (ULvl p, _) -> case lookup p fs of
        Just (VLvl l) -> go c (ELvl r p l) us ys
        _             -> Nothing
      (UDef{}, _) -> let (g, rest) = span isGroupUnit (u : us) in go c (mkGroup r g) rest ys
      (UMod{}, _) -> go c (mkGroup r [u]) us ys
      (UInst{}, _) -> go c (mkGroup r [u]) us ys
      _ -> go c r us ys
    go _ _ _ _ = Nothing
  VRec (Just _) tel r | length xs == length tel -> go cx r tel xs []
   where
    go c _ [] [] acc = Just (c, VStruct (reverse acc))
    go c rr ((l, a) : t) (y : ys) acc =
      let (c', g) = extVar c y (eval rr a) in go c' (EVar rr l g) t ys ((l, g) : acc)
    go _ _ _ _ _ = Nothing
  _ -> Nothing

checkSplit :: Cx -> Id -> [(Name, ([Name], [RecR], Exp))] -> [(Name, Tel)] -> Env -> Clos -> Res ()
-- every branch is for a constructor of the data type (an unknown one
-- would never be checked), and every constructor has its branch
checkSplit cx t bs cs r f
  | (c : _) <- [ c | (c, _) <- bs, c `notElem` map fst cs ] =
      failWith ("split: " ++ c ++ " is not a constructor of this data type")
  | otherwise = checkSplitAll cx t bs cs r f

checkSplitAll :: Cx -> Id -> [(Name, ([Name], [RecR], Exp))] -> [(Name, Tel)] -> Env -> Clos -> Res ()
checkSplitAll _ _ _ [] _ _ = ok
checkSplitAll cx t bs ((c, tel) : cs) r f = case lookup c bs of
  Nothing -> failWith ("split: missing the branch for " ++ c)
  Just (xs, rs, body) -> do
    (cx', vs) <- openTel cx xs tel r
    cx'' <- recCx cx' t c tel r f vs rs
    case check cx'' body (capp f (VCon c vs)) of
      Left msg -> failWith ("in the branch  " ++ c ++ "  of the split:\n" ++ msg)
      Right () -> ok
    checkSplitAll cx t bs cs r f

-- the recursive results of a branch, as variables of their types: for the
-- field x : d ps the result r : P x, for x : (ys : Psi) -> d ps the result
-- r : (ys : Psi) -> P (x ys), where P is the motive f
recCx :: Cx -> Id -> Name -> Tel -> Env -> Clos -> [Val] -> [RecR] -> Res Cx
recCx cx0 t c tel r f vs = foldl step (Right cx0)
 where
  step acc (RecR j n y) = do
    cx <- acc
    if j < 0 then failWith ("split: the recursive results of " ++ c ++ " are not annotated (internal)") else do
      let ty | n == 0 = capp f (vs !! j)
             | otherwise = eval (EVar (EVar (fieldEnv j) (recFld t c j) (vs !! j)) (recMot t c j) (VLam f))
                                (recTyExp t c j (snd (tel !! j)))
      Right (fst (extVar cx y ty))
  -- the environment of the field types before position j
  fieldEnv j = foldl (\e ((z, _), v) -> EVar e z v) r (take j (zip tel vs))

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
            UDef _ x a b -> do
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
enterGroup cx us = cx { cxEnv = r, cxTys = [ (i, eval r a) | UDef i _ a _ <- us ] ++ cxTys cx }
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
  go (EDecl r _ _) = go r
  go (ELvl r _ _) = go r
  go (EDef r _ _ fr) = case Map.lookup x (fIndex fr) of
    Just (EMod md) -> Right md
    Just _         -> failWith (x ++ " is not a module")
    Nothing        -> go r

showM :: MExp -> String
showM m = case m of
  MVar x    -> shortName x
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
    let cx' = cx { cxTh = addVar x (cxTh cx)
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
        a  = either (const (unfilledHoles a0)) id fa
        va = ev cx a
        -- a declared variable is not bound in the environment: it is
        -- itself (Wang: ()(x) = x), so it is never part of a dynamic part
        -- (a variable of segment type is bound to itself with the fields
        -- its type fixes,  c : M[x := e]  gives  c.x = e ; not dynamic)
        cx' = cx { cxEnv = case whnf Set.empty va of
                             VSegT md fs -> EDecl (cxEnv cx) x (VVar x md fs)
                             _          -> cxEnv cx
                 , cxTys = (x, va) : cxTys cx
                 , cxPSorts = (x, inferSort cx a) : cxPSorts cx }
        (cx'', evs, us') = checkUnitsF cx' us
    in (cx'', Event x (fmap (const []) (fa >> inCtx ("in the type of " ++ x) (checkType cx a))) : evs
       , UPar i x a : us')
  ULock s -> keep u (checkUnitsF cx { cxLocks = Set.fromList s } us)
  UDir d ->
    let (cx', evs, us') = checkUnitsF cx us
    in (cx', Event "#" (fillDir cx d >>= runDirective cx) : evs, u : us')
  UMod i x k mus0 ->
    let -- the body is checked in the context where it is declared; its
        -- parameters are rigid there.  Locks set inside persist.  The
        -- universe of the segment as a type is computed from the sorts of
        -- its parameters; the sorts of nested segments are kept (stated
        -- with this segment's level parameters, found in an instance).
        (cxIn, evsIn, mus) = checkUnitsF cx { cxPSorts = [] } mus0
        u' = UMod i x k mus
        cx1 = cx { cxEnv = mkGroup (cxEnv cx) [u'] }
        cx2 = cx1 { cxLocks = cxLocks cxIn, cxSegSort = (i, cxPSorts cxIn) : cxSegSort cxIn }
        (cx3, evs, us') = checkUnitsF cx2 us
    in (cx3, [ ev' { evLabel = x ++ "." ++ evLabel ev' } | ev' <- evsIn ] ++ evs, u' : us')
  UInst i x m0 ->
    let fm = fillM cx m0
        m  = either (const (unfilledM m0)) id fm
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
                     UDef _ x a b -> do
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
  Mem _ _ _ a  -> hasHole a
  Named _ a  -> hasHole a
  App a b      -> hasHole a || hasHole b
  Lam _ b      -> hasHole b
  Pi _ a b     -> hasHole a || hasHole b
  Let us b     -> any unitHole us || hasHole b
  Sum _ cs   -> any (any (hasHole . snd) . snd) cs
  Con _ as     -> any hasHole as
  -- a split whose recursive results are not yet annotated is filled too
  Split _ bs -> any (\(_, (_, rs, b)) -> any (\(RecR j _ _) -> j < 0) rs || hasHole b) bs
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
  UDef _ _ a b -> hasHole a || hasHole b
  UPar _ _ a     -> hasHole a
  _              -> False

-- fill in checking mode
fillC :: Cx -> Exp -> Val -> Res Exp
fillC cx e t0
  | not (hasHole e) = Right e
  | otherwise = case (e, t) of
      (_, VCPi cs a) -> fillC (addCs cx cs) e a
      (Named i e', _) -> fmap (Named i) (fillC cx e' t0)
      (Lam x b, VPi a f) -> let (cx', v) = extVar cx x a in fmap (Lam x) (fillC cx' b (capp f v))
      (LLam x b, VLPi f) -> let (cx', l) = extLvl cx x in fmap (LLam x) (fillC cx' b (lcapp f l))
      (Pi x a b, VU _) -> do a' <- fillC cx a t
                             b' <- fillC (fst (extVar cx x (ev cx a'))) b t
                             Right (Pi x a' b')
      (Sig x a b, VU _) -> do a' <- fillC cx a t
                              b' <- fillC (fst (extVar cx x (ev cx a'))) b t
                              Right (Sig x a' b')
      (Rec tel, VU _) -> fmap Rec (fillTelIn cx tel t)
      (Sum i cs, VU _) -> fmap (Sum i) (mapM (\(c, tel) -> fmap ((,) c) (fillTelIn cx tel t)) cs)
      (Pair a b, VSig _ ta f) -> do a' <- fillC cx a ta
                                    b' <- fillC cx b (capp f (ev cx a'))
                                    Right (Pair a' b')
      (Struct fs, VRec _ tel r) -> fmap Struct (fillStruct fs tel r)
      (Con c as, VSum _ _ cs r) -> case lookup c cs of
        Just tel -> fmap (Con c) (fillArgs as tel r)
        Nothing  -> Right e
      (Split i bs, VPi dom f) -> case force cx dom of
        VSum st _ cs r -> fmap (Split i) (mapM (fillBranch st cs r f) bs)
        d -> case bs of
          [(c, (xs, rs, b))] | Just (cx', el) <- recordBranch cx d xs ->
            fmap (\b' -> Split i [(c, (xs, rs, b'))]) (fillC cx' b (capp f el))
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
  fillBranch st cs r f (c, (xs, rs, body)) = case lookup c cs of
    Nothing -> Right (c, (xs, rs, body))
    Just tel -> do
      rs' <- annotate (sumDef st) c tel rs
      (cx', vs) <- openTel cx xs tel r
      cx'' <- recCx cx' st c tel r f vs rs'
      body' <- fillC cx'' body (capp f (VCon c vs))
      Right (c, (xs, rs', body'))
  -- the positions of the recursive fields, from the data type: an omitted
  -- list stays empty; a given one has one name per recursive field
  annotate d c tel rs
    | null rs = Right []
    | length rs /= length shapes =
        failWith ("the branch " ++ c ++ " names " ++ show (length rs) ++ " recursive results, but "
                  ++ c ++ " has " ++ show (length shapes) ++ " recursive fields")
    | otherwise = Right [ RecR j n y | ((j, n), RecR _ _ y) <- zip shapes rs ]
   where shapes = [ (j, n) | (j, (_, ta)) <- zip [0 ..] tel, Just n <- [recShape d ta] ]

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
      Named i e' -> fmap (Named i) (fillT cx e')
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
      -- a derived member of a record element  t.d : evaluation is untyped,
      -- so it is written with its record and head parameters,  R[ps].d at t
      -- (RECORDS.md §3); on a variable of record type, which carries its
      -- record, the projection itself computes the same value
      ProjU a l -> do
        (a', ta) <- fillI cx a
        case force cx ta of
          -- a field (or head parameter) the type fixes: its value (§4)
          -- (its type is the field's type, from the projection: the value
          -- itself may not be inferable, e.g. a constructor)
          VSegT _ fs | Just v <- lookup l fs, notLvl v, Just e' <- quote cx v -> do
            t <- inferD cx (Proj a' l)
            Right (e', t)
          VSegT md fs | isDerived md l ->
            case quote cx (VSegT md []) of
              Just (SegT me _) -> do
                args <- mapM (\p -> case lookup p fs of
                                 Just (VLvl lv) -> maybe (Left ("cannot write the level of " ++ p)) (Right . ALv)
                                                         (quote cx (VU lv) >>= \u -> case u of { U lv' -> Just lv'; _ -> Nothing })
                                 Just v -> maybe (Left ("cannot write the parameter " ++ p)) (Right . ATm) (quote cx v)
                                 Nothing -> Left ("the parameter " ++ p ++ " of the record is not known"))
                             (paramNames (headUnits md))
                retype (Right (Mem me args l a'))
              _ | VVar{} <- ev cx a' -> retype (Right (Proj a' l))
                | otherwise ->
                    failWith ("the member " ++ l ++ " of " ++ pretty a' ++ ": its record "
                              ++ shortId (modId md) ++ " cannot be named here (bring it into scope)")
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
  notLvl v = case v of { VLvl _ -> False; _ -> True }

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
    UDef i x a b ->
      let ta = inCtx ("in the type of " ++ x) (fillT cx1 a)
          a' = either (const (unfilledHoles a)) id ta
          tb = inCtx ("in the definition of " ++ x) (fillC cx1 b (ev cx1 a'))
      in (UDef i x a' (either (const (unfilledHoles b)) id tb), [ m | Left m <- [ta] ] ++ [ m | Left m <- [tb] ])
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
    VRef _ r -> any (ph n) (dynVals r)
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
      -- different heads: fall through (the heads are computed below)
    (VCon c as, VCon d bs) | c == d -> goList k as bs sols
    (VPair a b, VPair a' b') -> go k b b' (go k a a' sols)
    -- a pair pattern against a value that is not a pair: its projections
    -- (eta for Sigma; nothing is unfolded)
    (VPair a b, _) | notPair t -> go k b (vsnd t) (go k a (vfst t) sols)
    -- a projection of a hole determines only part of it (?m.1 = s.1 does
    -- not give ?m = s): nothing is learnt through a projection of a hole
    (VFst a, VFst b)       | not (isHoleV a) -> go k a b sols
    (VSnd a, VSnd b)       | not (isHoleV a) -> go k a b sols
    (VProj a l, VProj b l') | l == l' && not (isHoleV a) -> go k a b sols
    (VLApp a _, VLApp b _) -> go k a b sols
    (VRef u r, VRef u' r') | defId u == defId u' -> goList k (dynVals r) (dynVals r') sols
    (VSegT m fs, VSegT n gs) | modId m == modId n ->
      goList k (map snd fs) (map snd gs) (goList k (modDyn m) (modDyn n) sols)
    (VInst m r, VInst n r') | modId m == modId n ->
      goList k [ lookupDyn r x | x <- paramNames (modUnits m) ]
               [ lookupDyn r' x | x <- paramNames (modUnits n) ] sols
    (VSum i d _ _, VSum j d' _ _) | i == j -> goList k d d' sols
    -- different heads: the two sides are computed to weak head normal
    -- form WITHOUT unfolding any definition (the folded view: solutions are
    -- written with names), and compared again if one of them changed
    _ | t' <- whnfFolded t, p' <- whnfFolded p
      , progressed t t' || progressed p p' -> go k p' t' sols
      -- one side has a primitive head, the other is a defined constant:
      -- the constant is unfolded down to its head, as the checker does when
      -- it needs a Pi, a Sigma or an Id (never inside, never for a lock)
      | primHead p, t' <- whnf (cxLocks cx) t, progressed t t' -> go k p t' sols
      | primHead t, p' <- whnf (cxLocks cx) p, progressed p p' -> go k p' t sols
      | otherwise -> sols
  notPair v = case whnfFolded v of
    VPair{} -> False
    _       -> True
  primHead v = case v of
    VId{} -> True
    VPi{} -> True
    VSig{} -> True
    VU{} -> True
    VRec{} -> True
    VSum{} -> True
    VSegT{} -> True
    VLPi{} -> True
    VCPi{} -> True
    _ -> False
  isHoleV x = case x of
    VConst n [] -> take 2 n == "?m"
    _ -> False
  spineV v as = case v of
    VApp f a -> spineV f (a : as)
    _ -> (v, as)
  -- did weak head normalisation compute something (a definition unfolded,
  -- a projection or an application reduced)?
  progressed a b
    | VRef u _ <- fst (spineV a []) = case fst (spineV b []) of
        VRef u' _ -> defId u /= defId u'
        _             -> True
  progressed a b = case (a, b) of
    (VRef{}, VRef{}) -> False
    (VApp{}, VApp{}) -> False
    (VFst{}, VFst{}) -> False
    (VSnd{}, VSnd{}) -> False
    (VProj{}, VProj{}) -> False
    (VIdJ{}, VIdJ{}) -> False
    (VLApp{}, VLApp{}) -> False
    (VRef{}, _) -> True
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
    (VVar a _ _, VVar b _ _) | a == b -> Just sols
    (VRef u _, VRef u' _) | defId u == defId u' -> Just (go k hp ht sols)
    (VProj a l, VProj b l') | l == l' && not (isHoleV a) -> Just (go k a b sols)
    (VFst a, VFst b) | not (isHoleV a) -> Just (go k a b sols)
    (VSnd a, VSnd b) | not (isHoleV a) -> Just (go k a b sols)
    _ -> Nothing
  goList k as bs sols = foldl (\acc (a, b) -> go k a b acc) sols (zip as bs)
  under k f g sols = go (k + 1) (capp f (VGen k)) (capp g (VGen k)) sols

pname :: (Name, [Unit], Maybe Env) -> Name
pname (x, _, _) = x

-- Quoting: a value back to a term of the current scope.  Variables are
-- named by their binders; a definition, a segment or an element is
-- written by its name (directly, or as a member M[args].f of the segments
-- it belongs to, read off its id); fails rather than guess.
data QScope = QScope
  { scGens   :: [(Int, Name)]
  , scLvls   :: [(LName, Name)]
  , scUnfold :: Bool    -- a definition with no name: write its body instead
  , scCC     :: CC
  , scK      :: Int
  , scEnv    :: Env
  , scEtas   :: [(Val, Name)]       -- variables bound to elements built by new
  , scDecls :: Set.Set Name          -- the declared variables in scope
  , scInsts :: [(Id, Mod)] }        -- the instances in scope: aliases and
                                    -- segments without parameters

-- the group frame: its entries, by name and by unique id
data QFrag = QFrag { fIndex :: Map.Map Name Ent
                   , fDyn   :: [(Name, Val)] }   -- the dynamic part below the frame

fragOf :: Env -> [Unit] -> [(Name, Ent)] -> QFrag
fragOf rho us es = QFrag (Map.fromList (es ++ [ (unitIdOf u, e) | u <- us, let x = unitName u, x /= ""
                                                                , Just e <- [lookup x es] ]))
                         (case rho of { EDef r _ _ _ -> dynOf r ; _ -> [] })

scopeOf :: Cx -> QScope
scopeOf cx = go (cxEnv cx) (QScope [] [] True (cc cx) (cxK cx) (cxEnv cx) []
                             (Set.fromList (map fst (cxTys cx))) (instancesInScope (cxEnv cx)))
 where
  go r sc = case r of
    ENil -> sc
    EVar r' x v -> go r' (addVar' x v sc)
    EDecl r' _ _ -> go r' sc
    ELvl r' x l -> go r' (case latoms l of
                            [(n, 0)] -> sc { scLvls = scLvls sc ++ [(n, x)] }
                            _ -> sc)
    EDef r' _ _ _ -> go r' sc
  addVar' x v sc = case v of
    VGen i     -> sc { scGens = scGens sc ++ [(i, x)] }
    VVar n _ _ | take 2 n == "%v" -> sc { scGens = scGens sc ++ [(read (drop 2 n), x)] }
    -- a variable bound to an element built by new (a fixed field bound in
    -- a record branch): the element is written as the variable
    VInst m r  -> let sc1 = sc { scEtas = scEtas sc ++ [(v, x)] }
                  in case [ b | p <- termParams (modUnits m), VProj b q <- [lookupDyn r p], q == p ] of
                       (VGen i : _) -> sc1 { scGens = scGens sc1 ++ [(i, x)] }
                       _ -> sc1
    _ -> sc

-- the segments a declaration belongs to, outermost first, read off its id
--   A.B.f  ->  [A, A.B]
segChain :: Id -> [Id]
segChain i = case break (`elem` "/#\0") i of
  (p, "") -> prefixes (splitDots p)
  _       -> []                      -- a local definition: not a member
 where
  splitDots str = case break (== '.') str of
    (a, _ : b) -> a : splitDots b
    (a, [])    -> [a]
  prefixes xs = [ joinDots (take n xs) | n <- [1 .. length xs - 1] ]
  joinDots = foldr1 (\a b -> a ++ "." ++ b)

-- the instances in scope, by their ids: aliases (module N = M[..]) and
-- segments without parameters
instancesInScope :: Env -> [(Id, Mod)]
instancesInScope r = case r of
  ENil -> []
  EVar r' _ _ -> instancesInScope r'
  EDecl r' _ _ -> instancesInScope r'
  ELvl r' _ _ -> instancesInScope r'
  EDef r' us es _ -> [ (i, m) | u <- us, Just (i, x) <- [modUnitName u], Just (EMod m) <- [lookup x es]
                              , Just _ <- [modInst m] ] ++ instancesInScope r'

-- the id and name of a unit that is a segment or an alias
modUnitName :: Unit -> Maybe (Id, Name)
modUnitName u = case u of
  UInst i x _ -> Just (i, x)
  UMod i x _ _ -> Just (i, x)
  _           -> Nothing

-- a segment by its id, if it is in scope
lookupModM :: Env -> Id -> Maybe Mod
lookupModM r0 x = go r0
 where
  go ENil = Nothing
  go (EVar r _ _) = go r
  go (EDecl r _ _) = go r
  go (ELvl r _ _) = go r
  go (EDef r _ _ fr) = case Map.lookup x (fIndex fr) of
    Just (EMod m) -> Just m
    _             -> go r

lookupAnyE :: Env -> Name -> Maybe (Either Val Mod)
lookupAnyE r0 x = go r0
 where
  go ENil = Nothing
  go (EVar r y v) = if x == y then Just (Left v) else go r
  go (EDecl r y v) = if x == y then Just (Left v) else go r
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
    Named _ a  -> go bs a
    Let us b     -> let bs' = [ unitName u | u <- us ] ++ bs
                    in concat [ go bs' a ++ go bs' t | UDef _ _ a t <- us ] ++ go bs' b
    Sum _ cs   -> concat [ tel bs t | (_, t) <- cs ]
    Con _ as     -> concatMap (go bs) as
    Split _ br -> concat [ go (xs ++ recNames rs ++ bs) b | (_, (xs, rs, b)) <- br ]
    Pair a b     -> go bs a ++ go bs b
    Fst a        -> go bs a
    Snd a        -> go bs a
    Rec t        -> tel bs t
    Struct fs    -> concatMap (go bs . snd) fs
    Proj a _     -> go bs a
    ProjU a _    -> go bs a
    Mem m as _ a -> me bs m ++ concatMap (arg bs) as ++ go bs a
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
    VInst m r -> [ lookupDyn r x | x <- termParams (modUnits m) ]
    VPi a _ -> [a]
    VSig _ a _ -> [a]
    VId a x y -> [a, x, y]
    VPair a b -> [a, b]
    VFst a -> [a]
    VSnd a -> [a]
    VProj a _ -> [a]
    VCon _ as -> as
    _ -> []

-- PRIMREC.md 5.4, a test (--quote-test): a definition whose body is a
-- split, with a branch that has recursive results and whose body is again
-- a split (Ackermann).  That nested split, built with the CANONICAL
-- results, is written back as the definition applied to its path; built
-- with ABSTRACT results (fresh variables, as when the branch is checked or
-- in the conversion fallback), the read-back must refuse it.
quoteTest :: Cx -> Id -> [String]
quoteTest cx i = case whnf Set.empty (lookupVal (cxEnv cx) i) of
  f@(VSplit t _ bs rho) -> concat [ one f t rho c xs rs b | (c, (xs, rs@(_ : _), b)) <- bs ]
  _ -> ["not a split"]
 where
  k = cxK cx
  one f t rho c xs rs b =
    let n = length xs
        gens = [ VGen (k + j) | j <- [0 .. n - 1] ]
        rgens = [ VGen (k + n + j) | j <- [0 .. length rs - 1] ]
        canonical = eval (recBind t c f (bindAll rho xs gens) xs gens rs) b
        abstract = eval (bindAll (bindAll rho xs gens) (recNames rs) rgens) b
        sc = (scopeOf cx) { scGens = zip [k ..] (xs ++ recNames rs) ++ scGens (scopeOf cx)
                          , scK = k + n + length rs }
        shw v = case whnf Set.empty v of
          w@(VSplit{}) -> maybe "REFUSED (not written back)" pretty (quoteWith sc w)
          _ -> "the branch body is not a split"
    in [ "branch " ++ c ++ ", canonical recursive results:  " ++ shw canonical
       , "branch " ++ c ++ ", abstract recursive results:   " ++ shw abstract ]

quoteWith :: QScope -> Val -> Maybe Exp
quoteWith sc v0 = case v0 of
  VGen i -> fmap Var (lookup i (scGens sc))
  VVar x _ _ | take 2 x == "%v" -> fmap Var (lookup (read (drop 2 x)) (scGens sc))
           | otherwise -> Just (Var x)
  VConst i [] | Set.member i (scDecls sc) -> Just (Var i)   -- a declared variable in scope
  VU l -> fmap U (qLvl l)
  VLvl _ -> Nothing
  -- a definition: by its id if it means the same here, else as a member
  -- M[args].f of its segments; with no name, its body
  -- a derived member of a record:  R[ps].d at its element
  VRef u r | Just t <- lookup "%self" (allBound r)
           , (rid : _) <- reverse (segChain (defId u))
           , Just md <- lookupModM r rid -> do
    me <- segPath rid (modEnv md)
    as <- mapM (qArg . paramVal r) (paramNames (headUnits md))
    t' <- q t
    Just (Mem me as (unitName u) t')
  VRef u r -> let i = defId u in
    case lookupVal (scEnv sc) i of
      VRef u' r' | defId u' == i && convs (scCC sc) (dynVals r) (dynVals r') -> Just (Var i)
      _ -> case memberOf i (unitName u) r of
        Just h -> Just h
        Nothing | scUnfold sc -> quoteWith sc (unfoldRef u r)
                | otherwise -> Nothing
  VApp f a -> case appSpine v0 [] of
    -- an application of a definition: its name, found once, applied to
    -- the arguments; with no name here, its head normal form (never a
    -- redex with a lambda head)
    (hd@(VRef{}), as) -> case quoteWith sc { scUnfold = False } hd of
      Just h -> foldl App h <$> mapM q as
      Nothing | scUnfold sc -> quoteWith sc (whnf Set.empty v0)
              | otherwise -> Nothing
    _ -> App <$> q f <*> q a
  VPi a f -> binder (\x b -> Pi x <$> q a <*> b) f
  VSig (Just (i, _)) a (Clos x e r)
    | freeHere (filter (/= x) (freeNamesE e)) r ->
        (\a' -> Named i (Sig x a' e)) <$> q a
    | otherwise -> Nothing
  VRec (Just (i, _)) t r
    | freeHere (freeNamesE (Rec t)) r -> Just (Named i (Rec t))
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
  -- an element built by new: the variable bound to it, if any (only the
  -- same element: new R[r.x, c, d] is not r, though r.x is a field)
  VInst m r -> case [ x | (w, x) <- scEtas sc, eqVal w v0 ] of
    (x : _) -> Just (Var x)
    -- an element built with new: new M[args]
    [] -> do
      me <- segPath (modId m) (modEnv m)
      as <- mapM (qArg . lookupDyn r) (paramNames (modUnits m))
      Just (New (MApp me as))
  -- a segment type: the segment, reached from the segments in scope
  VSegT m fs -> do
    me <- segPath (modId m) (modEnv m)
    fs' <- mapM (\(x, a) -> fmap ((,) x) (qArg a)) fs
    Just (SegT me fs')
  VLApp a l -> LApp <$> q a <*> qLvl l
  -- a sum or split reached by unfolding: the name of the definition it is
  -- the body of (the resolver names them so), if that name evaluates to it
  -- a sum or a split: its definition applied to the values of its path
  -- (mTT10 section 5: R(B rho) = f_B (R rho)); never a redex
  VSum t _ _ r   -> byPath t r
  VSplit t _ _ r -> byPath t r
  _ -> Nothing
 where
  q = quoteWith sc
  k = scK sc
  binder mk f = let x = "h%" ++ show k
                    sc' = sc { scGens = (k, x) : scGens sc, scK = k + 1 }
                in mk x (quoteWith sc' (capp f (VGen k)))
  qLvl l = fmap (foldr1 LMax) (mapM atom (latoms l))
  atom (n, j) = fmap (\b -> iterate LSuc b !! j)
                     (if n == "0" then Just LZero else Just (maybe (LV n) LV (lookup n (scLvls sc))))
  qArg v = case v of
    VLvl l -> fmap ALv (qLvl l)
    _      -> fmap ATm (q v)
  -- the value of a parameter of a segment in an environment: its binding,
  -- or the variable itself
  paramVal r p = fromMaybe (VConst p []) (lookup p (allBound r))
  -- a member  M1[as1].M2[as2]...f : the segments it belongs to, from the
  -- innermost one that is in scope with the same enclosing parameters
  memberOf i x r = do
    me <- segPathIn True (segChain i) r
    Just (Acc me x)
  -- the segment itself (not applied: its fields are given apart)
  segPath sid r = segPathIn False (segChain sid ++ [sid]) r
  -- the segments of the chain, written from the innermost one in scope;
  -- each is applied to the values of its parameters in r
  segPathIn applyLast chain r = case [ (k, m) | (k, sid) <- reverse (zip [0 ..] chain)
                                    , Just m <- [lookupModM (scEnv sc) sid]
                                    , Just m' <- [lookupModM r sid]
                                    , modId m == modId m'
                                    , convs (scCC sc) (modDyn m) (modDyn m') ] of
    ((k, m0) : _) -> foldl step (Just (MVar (modId m0), m0)) (drop (k + 1) chain) >>= fin
    [] -> Nothing
   where
    -- enter the next segment: apply the current one to its parameters
    step acc sid = do
      (me, m) <- acc
      me' <- applied me m
      sub <- lookupModM r sid        -- an enclosing segment of the value
      Just (MSub me' (lastOf sid), sub)
    fin (me, m) = if applyLast then applied me m else Just me
    applied me m
      | hasParams (modUnits m) = case aliasFor m of
          Just a  -> Just a
          Nothing -> MApp me <$> mapM (qArg . paramVal r) (paramNames (modUnits m))
      | otherwise = Just me
    -- an instance of m in scope under an alias, with the same parameters
    -- an instance of m with the same context and parameters, reached from
    -- the instances in scope through the aliases and segments inside them
    -- (breadth first; each segment is entered once)
    aliasFor m = search [ (MVar i, a) | (i, a) <- scInsts sc ] Set.empty
     where
      search [] _ = Nothing
      search ((me, a) : rest) seen
        | matches a = Just me
        | Set.member (modId a) seen = search rest seen
        | otherwise = search (rest ++ inside me a) (Set.insert (modId a) seen)
      matches a = modId a == modId m && convs (scCC sc) (modDyn a) (modDyn m)
                  && case modInst a of
                       -- the parameters the value sees (in a segment, a
                       -- definition sees only the parameters before it)
                       Just ra -> and [ conv (scCC sc) (paramVal ra p) v | p <- paramNames (modUnits m)
                                                                         , Just v <- [lookup p (allBound r)] ]
                       Nothing -> False
      inside me a = case modInst a of
        Just ra -> [ (MSub me x, c) | u <- modUnits a, Just (_, x) <- [modUnitName u]
                                    , Just c <- [lookupModM ra x], Just _ <- [modInst c] ]
        Nothing -> []
    lastOf sid = reverse (takeWhile (/= '.') (reverse sid))
  byPath t r = case break (== '\0') t of
    (fid, _ : ps) -> do
      -- PRIMREC.md 5.4: the definition applied along the path is this value
      -- only when the recursive results bound on the path are the canonical
      -- ones (not the abstract ones of a branch being checked, or of the
      -- conversion fallback); otherwise the value is not written back
      if canonicalRecs fid (read ps :: [[String]]) then Just () else Nothing
      h <- quoteWith sc { scUnfold = False } (lookupVal r fid)
      let item e it = case it of
            ["v", x]      -> App e <$> q (lookupDyn r x)
            ["l", x]      -> LApp e <$> qLvl (lookupLvl r x)
            ("c" : c : ys) -> App e . Con c <$> mapM (q . lookupDyn r) ys
            _             -> Nothing
      foldl (\acc it -> acc >>= \e -> item e it) (Just h) (read ps :: [[String]])
    _ -> Nothing
   where
    canonicalRecs fid items = walk (unf (lookupVal r fid)) items
    unf = whnf Set.empty
    walk _ [] = True
    walk v (it : rest) = case it of
      ["v", x] -> walk (unf (app v (lookupDyn r x))) rest
      ["l", x] -> walk (unf (lapp v (lookupLvl r x))) rest
      ("c" : c : ys) -> case v of
        VSplit st _ bs rho | Just (_, rs, _) <- lookup c bs ->
          let vs = map (lookupDyn r) ys
              canon (RecR j n _)
                | n == 0 = app v (vs !! j)
                | otherwise = eval (EVar (bindAll rho ys vs) (recSelf st c j) v) (recLam st c j n (ys !! j))
          in and [ conv (scCC sc) (lookupDyn r y) (canon rr) | rr@(RecR _ _ y) <- rs ]
             && walk (unf (app v (VCon c vs))) rest
        _ -> False
      _ -> False
  -- the names of the original text mean here what they meant there
  freeHere ns r = and [ sameName n r | n <- ns ]
  sameName n r = case (lookupAnyE r n, lookupAnyE (scEnv sc) n) of
    (Just (Left v), Just (Left w)) -> conv (scCC sc) v w
    (Just (Right m), Just (Right m')) -> modId m == modId m' && convs (scCC sc) (modDyn m) (modDyn m')
    (Nothing, Nothing) -> True
    _ -> False
