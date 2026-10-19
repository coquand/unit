-- Term.hs -- strict positivity of data types and termination of recursive
-- definitions: a syntactic pass over the resolved units, after resolution
-- and before filling and checking, without evaluation.
--
--  * TWO RESTRICTIONS make the pass simple to justify.
--    (R1) Local definitions (let, where) appear only in the BODY of a
--         definition: not in the type of a definition or parameter, not in
--         a constructor field, a module argument or a directive.  So every
--         local definition is reached by the walk of a body below.
--    (R2) A constructor field mentions, of the definitions of its own group,
--         only data types.  So no alias of the group hides an occurrence of
--         a data type (Neg = D -> Empty ; data D = roll (k : Neg)), and the
--         type of a field calls no definition of the group.
--
--  * POSITIVITY.  In a constructor field, the data types of the group may
--    occur only strictly positively: never in the domain of a function
--    type, and never as an argument of another type (no nested types).
--
--  * TERMINATION, by size change (Lee, Jones, Ben-Amram; Abel's foetus).
--    An argument of a definition is a KEY (the definition, its position);
--    lambdas and splits of the canonical part of a body take the positions
--    in order (a split takes the next argument without naming it).  A
--    pattern variable of a data constructor is STRICTLY smaller than the
--    argument split; applying it keeps it smaller only for a recursive
--    field of function type (sup A f : f a), certified by positivity.  The
--    fields of a record are not smaller.  A projection of a term is a
--    component of it.  A local definition sees the arguments of the
--    definitions around it as further keys, unchanged by a call within the
--    same activation.  Every call gives a graph between the keys of the
--    caller and of the callee; the graphs of a recursive component are
--    closed under composition, and every idempotent loop must decrease
--    some key strictly.  A recursive definition used other than applied
--    (map f) is a call with unknown arguments, and fails.
--
--  * WHY EVERY CALL IS SEEN.  Calls in the types of definitions count,
--    with unknown arguments.  A hidden argument is filled from types: of
--    definitions (counted), of constructor fields (no call into the group,
--    R2), or of declarations made before the group.  Other accesses
--    (M[..].x, records, new) reach declarations made before the group,
--    which cannot call back into it.
--
-- PRIMREC (seg/primrec): recursion is only by eliminators and the scope
-- is sequential (SegParse), so termErrors is POSITIVITY only (with uniform
-- parameters, PRIMREC.md 2), enforced by the resolver and inside #fails.
-- The size-change pass is kept for --survey-termination and
-- --survey-primrec (migration aids).

module Term (positivityReport, terminationReport, restrictionReport, termErrors, primRecReport) where

import Seg
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Graph (stronglyConnComp, SCC(..))
import Data.List (intercalate)

------------------------------------------------------------------------
-- Subterms and occurrences

subExps :: Exp -> [Exp]
subExps e = case e of
  App a b -> [a, b]; Lam _ b -> [b]; Pi _ a b -> [a, b]
  Let us b -> concat [ [a, t] | UDef _ _ a t <- us ] ++ [b]
  Sum _ cs -> [ a | (_, tel) <- cs, (_, a) <- tel ]
  Con _ as -> as
  Split _ bs -> [ b | (_, (_, _, b)) <- bs ]
  Sig _ a b -> [a, b]; Pair a b -> [a, b]; Fst a -> [a]; Snd a -> [a]
  Rec t -> map snd t; Struct fs -> map snd fs; Proj a _ -> [a]; ProjU a _ -> [a]
  Id a x y -> [a, x, y]; Refl a -> [a]; IdJ a x c d y p -> [a, x, c, d, y, p]
  LPi _ a -> [a]; LLam _ a -> [a]; LApp a _ -> [a]; CPi _ a -> [a]
  Acc m _ -> mexps m
  SegT m fs -> mexps m ++ [ a | (_, ATm a) <- fs ]
  New m -> mexps m
  Mem m as _ a -> mexps m ++ [ x | ATm x <- as ] ++ [a]
  Named _ a -> [a]
  _ -> []

mexps :: MExp -> [Exp]
mexps m = case m of
  MVar _ -> []
  MSub n _ -> mexps n
  MApp n as -> mexps n ++ [ a | ATm a <- as ]

occurs :: Set.Set Id -> Exp -> Bool
occurs ids e = case e of
  Var x -> Set.member x ids
  _     -> any (occurs ids) (subExps e)

-- the head and the term arguments (level applications skipped)
spineT :: Exp -> (Exp, [Exp])
spineT e0 = go e0 []
 where
  go (App a b) as = go a (b : as)
  go (LApp a _) as = go a as
  go h as = (h, as)

-- the definitions of a list of units, by groups (consecutive definitions),
-- everywhere: in modules, records and lets
groups :: [Unit] -> [[Unit]]
groups [] = []
groups us@(u : rest) = case u of
  UDef{} -> let (g, rest') = span isGroupUnit us
            in g : concatMap inUnit g ++ groups rest'
  _ -> inUnit u ++ groups rest
 where
  inUnit v = case v of
    UDef _ _ a b -> inExp a ++ inExp b
    UPar _ _ a -> inExp a
    UMod _ _ _ vs -> groups vs
    _ -> []
  inExp e = case e of
    Let vs b -> groups vs ++ inExp b
    _ -> concatMap inExp (subExps e)

-- the body of a data definition: its constructors
dataBody :: Exp -> Maybe [(Name, Tel)]
dataBody e = case e of
  Lam _ b -> dataBody b
  LLam _ b -> dataBody b
  Sum _ cs -> Just cs
  _ -> Nothing

------------------------------------------------------------------------
-- Positivity

positivityReport :: [Unit] -> [String]
positivityReport us =
  [ shortName x ++ "." ++ c ++ ": " ++ msg ++ " in the field " ++ f
  | g <- groups us
  , let ids = dataIds g
  , not (Set.null ids)
  , UDef i x _ b <- g, Just cs <- [dataBody b]
  , let ps = dataParams b
  , (c, tel) <- cs, (f, t) <- tel
  , Just msg <- [fieldError i ps t] ]

-- the parameters of a data definition (its lambdas): terms and levels
dataParams :: Exp -> [Either Name Name]
dataParams e = case e of
  Lam x b -> Left x : dataParams b
  LLam x b -> Right x : dataParams b
  _ -> []

-- PRIMREC.md 2: a field mentions its data type d only as  d ps  or
-- (ys : Psi) -> d ps , Psi not mentioning d, ps exactly the parameters
fieldError :: Id -> [Either Name Name] -> Exp -> Maybe String
fieldError d ps t
  | not (occurs ds t) = Nothing
  | otherwise = case t of
      Pi _ a b | occurs ds a -> Just (shortName d ++ " occurs not strictly positively")
               | otherwise -> fieldError d ps b
      _ -> case fullSpine t [] of
             (Var i, as) | i == d ->
               if map toP as == ps then Nothing
               else Just (shortName d ++ " is not applied to exactly its parameters")
             _ -> Just (shortName d ++ " occurs not strictly positively (only " ++ shortName d
                        ++ " ps or (ys : Psi) -> " ++ shortName d ++ " ps)")
 where
  ds = Set.singleton d
  toP a = case a of
    Left (Var x) -> Left x
    Right (LV x) -> Right x
    _ -> Left "?"
  fullSpine e acc = case e of
    App a b -> fullSpine a (Left b : acc)
    LApp a l -> fullSpine a (Right l : acc)
    _ -> (e, acc)

dataIds :: [Unit] -> Set.Set Id
dataIds g = Set.fromList [ i | UDef i _ _ b <- g, Just _ <- [dataBody b] ]

positive :: Set.Set Id -> Exp -> Bool
positive ids t
  | not (occurs ids t) = True
  | otherwise = case t of
      Pi _ a b -> not (occurs ids a) && positive ids b
      LPi _ a  -> positive ids a
      CPi _ a  -> positive ids a
      _ -> case spineT t of
             (Var i, as) -> Set.member i ids && not (any (occurs ids) as)
             _ -> False

------------------------------------------------------------------------
-- The restrictions R1 and R2

restrictionReport :: [Unit] -> [String]
restrictionReport us = r1 us ++ r2
 where
  r2 = [ shortName x ++ "." ++ c ++ ": the field " ++ f ++ " mentions " ++ shortName j
         ++ ", a definition of the same group that is not a data type"
       | g <- groups us
       , let others = Set.fromList [ i | UDef i _ _ _ <- g ] `Set.difference` dataIds g
       , UDef _ x _ b <- g, Just cs <- [dataBody b]
       , (c, tel) <- cs, (f, t) <- tel, j <- take 1 (Set.toList (Set.filter (\i -> occurs (Set.singleton i) t) others)) ]
  r1 = concatMap unit
  unit u = case u of
    UDef _ x a b -> noLet ("the type of " ++ x) a ++ body x b
    UPar _ x a -> noLet ("the type of " ++ x) a
    UMod _ _ _ vs -> r1 vs
    UInst _ x m -> concatMap (noLet ("the arguments of " ++ x)) (mexps m)
    UDir d -> case d of
      DNormal e -> noLet "a directive" e
      DType e -> noLet "a directive" e
      DConv a b -> noLet "a directive" a ++ noLet "a directive" b
      DFails _ -> []
    _ -> []
  -- in a body: the local definitions are checked as units; a data type's
  -- fields are not a body
  body x e = case e of
    Sum _ cs -> concat [ noLet ("a field of " ++ x) t | (_, tel) <- cs, (_, t) <- tel ]
    Let vs b -> r1 vs ++ body x b
    _ -> concatMap (body x) (subExps e)
  noLet w e = [ "a local definition (let, where) in " ++ shortName w | hasLet e ]
  hasLet e = case e of
    Let _ _ -> True
    _ -> any hasLet (subExps e)

------------------------------------------------------------------------
-- Enforcement: the errors of the units  part  of the program  whole
-- (the constructors of the whole program give the sizes)

termErrors :: [Unit] -> [Unit] -> [String]
termErrors _ part = positivityReport part

------------------------------------------------------------------------
-- Termination

type Key = (Id, Int)               -- the k-th argument of a definition

-- what a term is, relative to the keys in scope: strictly smaller (True)
-- or a component (False); applying it keeps it so when iApp.  A pattern
-- variable also remembers its pattern (the key split, the constructor, the
-- position): the constructor applied to the pattern variables in order is
-- the argument split itself (ack m (ack (suc m) n)).
data Info = Info [(Key, Bool)] Bool (Maybe (Key, Name, Int))

iSize :: Info -> [(Key, Bool)]
iSize (Info s _ _) = s

type SEnv = Map.Map Name Info

-- a call: the caller and its enclosing definitions, the callee, the sizes
-- of the arguments; and for the primitive-recursion survey the arguments,
-- the variables in scope, and whether the call is in a type
data Raw = Raw [Id] Id [[(Key, Bool)]] [Exp] SEnv Bool

-- a definition: its name, its enclosing definitions, its number of keys
data Def = Def { dfName :: Name, dfAnc :: [Id], dfArity :: Int }

-- the tables of the walk: the constructors (for sizes), the definitions
data W = W { wCons :: Cons, wDefs :: Set.Set Id }

-- the fields of each constructor (name, arity): does applying the field
-- keep it smaller.  Ambiguous names that disagree are dropped.
type Cons = Map.Map (Name, Int) [Bool]

consTable :: [Unit] -> Cons
consTable us = Map.mapMaybe agree (Map.fromListWith (++) entries)
 where
  entries = [ ((c, length tel), [map (recFun ids . snd) tel])
            | g <- groups us
            , let ids = dataIds g
            , UDef _ _ _ b <- g, Just cs <- [dataBody b], positiveCons ids cs
            , (c, tel) <- cs ]
  positiveCons ids cs = and [ positive ids t | (_, tel) <- cs, (_, t) <- tel ]
  agree fs = case fs of
    (f : rest) | all (== f) rest -> Just f
    _ -> Nothing
  -- a recursive field of function type: its codomain is a type of the group
  recFun ids t = case t of
    Pi _ _ b -> codHead ids b
    _ -> False
  codHead ids t = case t of
    Pi _ _ b -> codHead ids b
    _ -> case spineT t of
           (Var i, _) -> Set.member i ids
           _ -> False

terminationReport :: [Unit] -> [String]
terminationReport us = terminationIn us us

terminationIn :: [Unit] -> [Unit] -> [String]
terminationIn whole us = concatMap verdict sccs
 where
  cons = consTable whole
  defIds = Set.fromList [ i | g <- groups us, UDef i _ _ _ <- g ]
  (defs, raws) = walkUnits (W cons defIds) [] Map.empty us
  defMap = Map.fromList defs
  calls = [ (head ch, callee, arcsOf ch callee szs) | Raw ch callee szs _ _ _ <- raws ]
  arcsOf _ callee szs =
    normG ([ (k, s, (callee, j)) | (j, sz) <- zip [0 ..] szs, (k, s) <- sz ]
           ++ [ ((a, j), False, (a, j)) | a <- ancOf callee, j <- [0 .. arityOf a - 1] ])
  ancOf i = maybe [] dfAnc (Map.lookup i defMap)
  arityOf i = maybe 0 dfArity (Map.lookup i defMap)
  nameOf i = maybe (shortName i) (shortName . dfName) (Map.lookup i defMap)
  outEdges = Map.fromListWith (++) [ (f, [t]) | (f, t, _) <- calls ]
  sccs = stronglyConnComp [ (i, i, Map.findWithDefault [] i outEdges) | (i, _) <- defs ]
  verdict scc = case scc of
    AcyclicSCC _ -> []
    CyclicSCC is ->
      let inC = Set.fromList is
          cs = [ (f, t, g) | (f, t, g) <- calls, Set.member f inC, Set.member t inC ]
          names = intercalate ", " (map nameOf is)
      in case sizeChange cs of
           Nothing -> ["recursive  " ++ names ++ ": terminates"]
           Just (f, g) -> ["recursive  " ++ names ++ ": NOT SHOWN TO TERMINATE, loop at "
                           ++ nameOf f ++ " " ++ showG g]
  showG g = "{" ++ intercalate ", " [ showK a ++ (if s then " > " else " >= ") ++ showK b
                                    | ((a, b), s) <- Map.toList g ] ++ "}"
  showK (i, k) = nameOf i ++ "#" ++ show k

-- a size-change graph: for each pair of keys (before, after), strict or not
type G = Map.Map (Key, Key) Bool

normG :: [(Key, Bool, Key)] -> G
normG arcs = Map.fromListWith (||) [ ((a, b), s) | (a, s, b) <- arcs ]

compose :: G -> G -> G
compose g1 g2 = Map.fromListWith (||)
  [ ((a, c), s1 || s2) | ((a, b), s1) <- Map.toList g1, ((b', c), s2) <- Map.toList g2, b == b' ]

-- the closure of the call graphs of a component; Nothing when every
-- idempotent loop decreases, otherwise a loop that does not
sizeChange :: [(Id, Id, G)] -> Maybe (Id, G)
sizeChange cs0 = go (Set.fromList [ (f, t, Map.toList g) | (f, t, g) <- cs0 ]) (map toS cs0)
 where
  toS (f, t, g) = (f, t, Map.toList g)
  go seen [] = check (Set.toList seen)
  go seen (new@(f, t, g) : rest)
    | Set.size seen > 20000 = Just (f, Map.fromList g)       -- give up
    | otherwise =
        let succs = [ (f, t', Map.toList (compose (Map.fromList g) (Map.fromList g')))
                    | (f', t', g') <- Set.toList seen, f' == t ]
                    ++ [ (f'', t, Map.toList (compose (Map.fromList g'') (Map.fromList g)))
                       | (f'', t'', g'') <- Set.toList seen, t'' == f ]
            fresh = [ x | x <- succs, not (Set.member x seen) ]
            seen' = foldr Set.insert seen fresh
        in new `seq` go seen' (rest ++ fresh)
  check xs = case [ (f, g) | (f, t, gl) <- xs, f == t, let g = Map.fromList gl
                           , compose g g == g
                           , not (or [ s | ((a, b), s) <- gl, a == b, s ]) ] of
    [] -> Nothing
    (x : _) -> Just x

-- the definitions and the calls of a list of units; anc: the enclosing
-- definitions (innermost first), env: the sizes of the variables in scope
walkUnits :: W -> [Id] -> SEnv -> [Unit] -> ([(Id, Def)], [Raw])
walkUnits w anc env = foldr add ([], []) . map unit
 where
  add (a, b) (c, d) = (a ++ c, b ++ d)
  unit u = case u of
    UDef i x a b ->
      let ch = i : anc
          tyCalls = [ Raw c t z as r True | Raw c t z as r _ <- expr w ch env a ]
          (n, ds, rs) = canon w ch 0 env b
      in ((i, Def x anc n) : ds, tyCalls ++ rs)
    UMod _ _ _ vs -> walkUnits w anc env vs
    _ -> ([], [])

-- the canonical part of a body: lambdas, splits, lets; returns the number
-- of keys taken
canon :: W -> [Id] -> Int -> SEnv -> Exp -> (Int, [(Id, Def)], [Raw])
canon w ch k env e = case e of
  Lam x b -> canon w ch (k + 1) (Map.insert x (Info [((d, k), False)] False Nothing) env) b
  LLam _ b -> canon w ch k env b
  Named _ b -> canon w ch k env b
  Split _ bs ->
    let rs = [ canon w ch (k + 1) (branchEnv c xs) b | (c, (xs, _, b)) <- bs ]
    in (maximum ((k + 1) : [ n | (n, _, _) <- rs ]), concat [ ds | (_, ds, _) <- rs ]
       , concat [ r | (_, _, r) <- rs ])
  -- a data type: its fields call no definition of the group (R2), and the
  -- data types they mention are positivity's
  Sum _ _ -> (k, [], [])
  Let us b ->
    let (ds, rs) = walkUnits w ch env us
        (n, ds', rs') = canon w ch k env b
    in (n, ds ++ ds', rs ++ rs')
  _ -> (k, localDefs, expr w ch env e)
 where
  d = head ch
  branchEnv c xs = case Map.lookup (c, length xs) (wCons w) of
    Just fs -> foldr (\(j, x, ap) -> Map.insert x (Info [((d, k), True)] ap (Just ((d, k), c, j)))) env
                     (zip3 [0 ..] xs fs)
    Nothing -> env                            -- a record, or unknown
  localDefs = letDefs e
  letDefs x = case x of
    Let vs b -> fst (walkUnits w ch env vs) ++ letDefs b
    _ -> concatMap letDefs (subExps x)

-- the calls in an expression (not in a canonical position)
expr :: W -> [Id] -> SEnv -> Exp -> [Raw]
expr w ch env e = case spineT e of
  (Var i, as) | Set.member i (wDefs w) ->
    Raw ch i (map (size env) as) as env False : concatMap (expr w ch env) as
  (h, as@(_ : _)) -> expr w ch env h ++ concatMap (expr w ch env) as
  _ -> case e of
    Let us b -> snd (walkUnits w ch env us) ++ expr w ch env b
    _ -> concatMap (expr w ch env) (subExps e)

size :: SEnv -> Exp -> [(Key, Bool)]
size env e = case e of
  Var x -> maybe [] iSize (Map.lookup x env)
  Fst a -> size env a
  Snd a -> size env a
  Proj a _ -> size env a
  ProjU a _ -> size env a
  Named _ a -> size env a
  Con c as | Just key <- rebuilt c as -> [(key, False)]
  _ -> case spineT e of
         (Var x, _ : _) | Just (Info s True _) <- Map.lookup x env -> s
         _ -> []
 where
  rebuilt c as = case [ p | Var x <- as, Just (Info _ _ (Just p)) <- [Map.lookup x env] ] of
    ps@((key, c', _) : _) | length ps == length as, c' == c
                          , ps == [ (key, c, j) | j <- [0 .. length as - 1] ] -> Just key
    _ -> Nothing

------------------------------------------------------------------------
-- Survey: which recursive definitions are primitive recursion with
-- parameters.  A self-call of f is DIRECT when, for some split of f at
-- position p, the argument p is a recursive field of that split (m, or
-- f' a for a function field f'), and every argument before p is f's own
-- (its parameter, or the constructor of an earlier split rebuilt): it is
-- then the recursive result of that field (the arguments after p are the
-- motive's).  A component is DIRECT when it is one definition whose
-- self-calls are all direct.  Also: forward references inside a group
-- that are on no cycle (reordering only).

primRecReport :: [Unit] -> [String]
primRecReport us =
  let forwards = forwardsOf us in
  concatMap verdict sccs
  ++ [ "forward    " ++ shortName x ++ " refers to the later " ++ intercalate ", " (map nameOf js)
     | (i, x, js0) <- forwards, let js = [ j | j <- js0, not (sameScc i j) ], not (null js) ]
  ++ [ show (length [ () | v <- map verdict sccs, any (isPrefixOf' "direct") v ]) ++ " direct, "
       ++ show (length [ () | v <- map verdict sccs, any (isPrefixOf' "OTHER") v ]) ++ " other, "
       ++ show (length [ () | (i, _, js) <- forwards, any (not . sameScc i) js ])
       ++ " definitions with forward references off cycles" ]
 where
  cons = consTable us
  defIds = Set.fromList [ i | g <- groups us, UDef i _ _ _ <- g ]
  (defs, raws) = walkUnits (W cons defIds) [] Map.empty us
  defMap = Map.fromList defs
  nameOf i = maybe (shortName i) (shortName . dfName) (Map.lookup i defMap)
  edges = Map.fromListWith (++) [ (head ch, [t]) | Raw ch t _ _ _ _ <- raws ]
  sccs = stronglyConnComp [ (i, i, Map.findWithDefault [] i edges) | (i, _) <- defs ]
  sccOf = Map.fromList [ (i, n) | (n, CyclicSCC is) <- zip [0 :: Int ..] sccs, i <- is ]
  sameScc i j = i == j || (Map.lookup i sccOf == Map.lookup j sccOf && Map.member i sccOf)
  isPrefixOf' a b = take (length a) b == a
  verdict scc = case scc of
    AcyclicSCC _ -> []
    CyclicSCC [f] ->
      let bad = [ (r, why) | r@(Raw ch t _ _ _ _) <- raws, t == f, f `elem` ch
                           , Just why <- [notDirect f r] ]
      in case bad of
           [] -> ["direct     " ++ nameOf f]
           ((r, why) : _) -> ["OTHER      " ++ nameOf f ++ ": " ++ why ++ "\n             " ++ showCall r
                              ++ (if length bad > 1 then "  (" ++ show (length bad) ++ " such calls)" else "")]
    CyclicSCC is ->
      let inC = Set.fromList is
          r = head ([ x | x@(Raw ch t _ _ _ _) <- raws, Set.member t inC, Set.member (head ch) inC, head ch /= t ] ++
                    [ x | x@(Raw ch t _ _ _ _) <- raws, Set.member t inC, Set.member (head ch) inC ])
      in ["OTHER      " ++ intercalate ", " (map nameOf is) ++ ": mutual (" ++ show (length is) ++ " definitions)"
          ++ "\n             " ++ showCall r]
  showCall (Raw ch t _ as _ ty) = "in " ++ nameOf (head ch) ++ (if ty then " (its type)" else "") ++ ":  "
    ++ take 160 (unwords (words (pretty (foldl App (Var (nameOf t)) as))))
  notDirect f (Raw ch _ _ as env ty)
    | ty = Just "a call in a type"
    | null as = Just "used without arguments"
    | otherwise =
        let ok p = p < length as && immediate f p env (as !! p)
                   && and [ identical f j env (as !! j) | j <- [0 .. p - 1] ]
            ps = [ p | p <- [0 .. length as - 1], ok p ]
        in if not (null ps) then Nothing
           else Just (reason f (head ch) env as)
  reason f caller env as
    | caller /= f, any (deeperLocal caller env) as = "a call from the local " ++ nameOf caller ++ " on its own pattern"
    | any (\(j, a) -> not (identical f j env a) && not (immediate f j env a) && smaller f j env a) (zip [0 ..] as) =
        "a smaller argument that is not a field of the split"
    | otherwise = "no argument is a field of a split of " ++ nameOf f ++ " with the arguments before it unchanged"
  deeperLocal caller env a = any (\(k, _) -> fst k == caller) (size env a)
  smaller f j env a = ((f, j), True) `elem` size env a

-- an argument p of a self-call of f is a recursive field of f's split at p
immediate :: Id -> Int -> SEnv -> Exp -> Bool
immediate f p env a = case spineT a of
  (Var x, args) | Just (Info _ ap (Just (key, _, _))) <- Map.lookup x env ->
    key == (f, p) && (null args || ap)
  _ -> False

-- an argument j of a self-call of f is f's own argument j
identical :: Id -> Int -> SEnv -> Exp -> Bool
identical f j env a = case a of
  Var x | Just (Info [(key, False)] _ Nothing) <- Map.lookup x env -> key == (f, j)
  Con _ _ -> size env a == [((f, j), False)]
  _ -> False

-- definitions referring to later members of their group (data types
-- excepted: they refer to each other by positivity's rules)
forwardsOf :: [Unit] -> [(Id, Name, [Id])]
forwardsOf us =
  [ (i, x, js)
  | g <- groups us
  , (n, UDef i x a b) <- zip [0 :: Int ..] g, Nothing <- [dataBody b]
  , let later = Set.fromList [ j | (m, UDef j _ _ _) <- zip [0 ..] g, m > n ]
        js = Set.toList (Set.fromList (filter (`Set.member` later) (vars a ++ vars b)))
  , not (null js) ]
 where
  vars e = case e of
    Var x -> [x]
    _ -> concatMap vars (subExps e)
