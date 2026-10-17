-- SegParse.hs -- lexer, parser and resolver.
--
-- Concrete syntax (braces and semicolons, no layout; cubicaltt order):
--
--   level a b ;                         level variables
--   constraint a < b, c <= d \/ a ;     level constraints
--   x (tel) : A ;                       a parameter / primitive notion
--   f (tel) : A = e ;                   a definition (body: expr or split,
--   f (tel) : A = e where { units } ;     optionally with a where block)
--   data D (tel) : U l = c1 (tel) | c2 ;   a labelled sum (": U l" optional:
--                                       without it, D is small, in every U)
--   module M (tel) { units } ;          a segment (the telescope = leading
--                                       parameters; body-less units inside
--                                       are parameters too)
--   module N = M[args] ;                an instance
--   open M ;  open M[args] ;            short names for the members
--   import F ;                          the file F.seg, as  module F { .. }
--   opaque f ;  transparent f ;  transparent_all ;
--   #normal e ; #type e ; #conv e = e ; #fails { units } ;
--
-- Telescopes:  (x y : A)  (a b : Level)  (a < b, b <= c)
-- Expressions: U l | [a b] A | [a < b] A | <a b> t | t @l | \ x -> e
--   | (tel) -> B | A -> B | (tel) * B | A * B | (a, b) | e.1 | e.2 | e.l
--   | M[args].x | sig { l : A ; .. } | struct { l = e ; .. }
--   | Id A a b | refl a | idJ A a C d b p | let { units } in e | split {..}
-- Levels: a | l+ | l \/ m.
--
-- The resolver turns the raw syntax into Seg's core: it decides what a
-- name is (variable, definition, level, module, opened member,
-- constructor) from scope alone, gives every declaration its qualified id,
-- and computes the dependencies (the dynamic part) of every definition,
-- labelled sum and split.  It needs no types: the core is untouched.

module SegParse (parseUnits, resolveProgram, RUnit(..)) where

import Seg
import Data.Char (isAlpha, isDigit, isSpace)
import Data.List (nub, (\\))
import qualified Data.Map.Strict as M

------------------------------------------------------------------------
-- Tokens

data Tok = TId String | TSym String | TProj String
  deriving (Eq, Show)

symbols :: [String]
symbols = ["->", "\\/", "<=", ":=", ".1", ".2", "(", ")", "{", "}", "[", "]", ";", ",",
           ":", "=", "\\", "|", "*", "#", "@", "<", ">", "+"]

lexer :: String -> Either String [Tok]
lexer [] = Right []
lexer s@(c : cs)
  | isSpace c = lexer cs
  | c == '-', take 1 cs == "-" = lexer (dropWhile (/= '\n') cs)
  | take 2 s == "{-" = block (0 :: Int) (drop 2 s)
  | c == '.', (d : _) <- cs, isAlpha d || d == '_' =
      let (w, rest) = ident1 cs in fmap (TProj w :) (lexer rest)
  | isAlpha c || c == '_' =
      let (w, rest) = ident1 s in fmap (TId w :) (lexer rest)
  | otherwise =
      case [ sy | sy <- symbols, take (length sy) s == sy ] of
        (sy : _) -> fmap (TSym sy :) (lexer (drop (length sy) s))
        []       -> Left ("unexpected character " ++ show c)
 where
  isIdent x = isAlpha x || isDigit x || x == '_' || x == '\''
  ident1 t = case span isIdent t of
    (w, '-' : d : rest) | isIdent d -> let (w', rest') = ident1 (d : rest)
                                       in (w ++ "-" ++ w', rest')
    (w, rest) -> (w, rest)
  block _ [] = Left "unterminated {- comment"
  block n t
    | take 2 t == "-}" = if n == 0 then lexer (drop 2 t) else block (n-1) (drop 2 t)
    | take 2 t == "{-" = block (n+1) (drop 2 t)
    | otherwise        = block n (tail t)

------------------------------------------------------------------------
-- Raw syntax

data R
  = RVar Name
  | RU R
  | RApp R R
  | RLApp R R
  | RLam [Name] R
  | RPi [TItem] R
  | RArr R R
  | RSig [TItem] R
  | RTimes R R
  | RLet [RUnit] R
  | RTuple [R]
  | RFst R | RSnd R
  | RDot R Name
  | RInst R [(Maybe Name, R)]                -- M[a, x := b]
  | RNew R
  | RHid R                                   -- {e}: a hidden argument given
  | RHole                                    -- _ : an argument to be inferred
  | RSplit Int [(Name, [Name], RBody)]
  | RRec [(Name, R)]
  | RStruct [(Name, R)]
  | RId R R R | RRefl R | RIdJ R R R R R R
  | RSuc R | RMax R R
  | RLPi [Name] R | RCPi [RCs] R | RLLam [Name] R
  deriving (Show)

data RCs = RCs R Rel R deriving (Show)

data TItem = TVars [Name] R | TVarsH [Name] R | TLvls [Name] | TCs [RCs]
  deriving (Show)

data RBody = RBody R [RUnit]                 -- an expression and its where block
  deriving (Show)

data RUnit
  = RDef Int Name [TItem] R (Maybe RBody)   -- occurrence, name, tel, type, body
  | RData Int Name [TItem] (Maybe R) [(Name, [TItem])]
  | RLevel [Name]
  | RCstr [RCs]
  | RModule Name [TItem] [RUnit]
  | RModInst Name R
  | ROpen Int R
  | RImport Name
  | ROpaque R | RTransparent R | RTransAll
  | RNormal R | RType R | RConv R R | RFails [RUnit]
  deriving (Show)

------------------------------------------------------------------------
-- Parser combinators, as in mtt: a function from tokens to a value and
-- the rest, failing with what was expected and where.

type P a = [Tok] -> Either String (a, [Tok])

expected :: String -> [Tok] -> Either String a
expected what ts = Left (what ++ " expected, found: " ++ shown)
 where shown = if null ts then "<end of input>" else unwords (map render (take 8 ts))

render :: Tok -> String
render (TId x)   = x
render (TSym x)  = x
render (TProj x) = "." ++ x

sym :: String -> P ()
sym x (TSym y : ts) | x == y = Right ((), ts)
sym x ts                     = expected ("'" ++ x ++ "'") ts

isSym :: String -> [Tok] -> Bool
isSym x (TSym y : _) = x == y
isSym _ _            = False

isKw :: String -> [Tok] -> Bool
isKw x (TId y : _) = x == y
isKw _ _           = False

kw :: String -> P ()
kw x (TId y : ts) | x == y = Right ((), ts)
kw x ts = expected ("'" ++ x ++ "'") ts

keywords :: [Name]
keywords = ["data", "split", "where", "let", "in", "U", "Id", "refl", "idJ",
            "opaque", "transparent", "transparent_all", "module", "open", "import",
            "level", "constraint", "sig", "struct", "normal", "type", "fails", "conv", "new", "calc"]

ident :: P Name
ident (TId x : ts) | x `notElem` keywords = Right (x, ts)
ident ts = expected "an identifier" ts

many1 :: P a -> P [a]
many1 p ts = do
  (x, ts1) <- p ts
  case p ts1 of
    Left _ -> Right ([x], ts1)
    Right _ -> do (xs, ts2) <- many1 p ts1
                  Right (x : xs, ts2)

manyP :: P a -> P [a]
manyP p ts = case p ts of
  Left _ -> Right ([], ts)
  Right (x, ts1) -> do (xs, ts2) <- manyP p ts1; Right (x : xs, ts2)

occ :: [Tok] -> Int
occ = length

------------------------------------------------------------------------
-- Telescopes

telescope :: P [TItem]
telescope ts
  | isSym "{" ts, Right (g, ts1) <- hidden ts = do
      (rest, ts2) <- telescope ts1
      Right (g : rest, ts2)
  | isSym "(" ts = case group ts of
      Left _ -> Right ([], ts)
      Right (g, ts1) -> do (rest, ts2) <- telescope ts1
                           Right (g : rest, ts2)
  | otherwise = Right ([], ts)
 where
  group ts0 = case binders ts0 of
    Right r -> Right r
    Left _  -> do
      ((), ts1) <- sym "(" ts0
      (cs, ts2) <- constraints ts1
      ((), ts3) <- sym ")" ts2
      Right (TCs cs, ts3)
  hidden ts0 = do
    ((), ts1) <- sym "{" ts0
    (xs, ts2) <- many1 ident ts1
    ((), ts3) <- sym ":" ts2
    (a, ts4)  <- expr ts3
    ((), ts5) <- sym "}" ts4
    Right (TVarsH xs a, ts5)
  binders ts0 = do
    ((), ts1) <- sym "(" ts0
    (xs, ts2) <- many1 ident ts1
    ((), ts3) <- sym ":" ts2
    if isKw "Level" ts3
      then do ((), ts4) <- kw "Level" ts3
              ((), ts5) <- sym ")" ts4
              Right (TLvls xs, ts5)
      else do (a, ts4) <- expr ts3
              ((), ts5) <- sym ")" ts4
              Right (TVars xs a, ts5)

constraints :: P [RCs]
constraints ts = do
  (c, ts1) <- constraint1 ts
  if isSym "," ts1
    then do ((), ts2) <- sym "," ts1
            (cs, ts3) <- constraints ts2
            Right (c : cs, ts3)
    else Right ([c], ts1)

constraint1 :: P RCs
constraint1 ts = do
  (l, ts1) <- exprJ ts
  (rel, ts2) <- case ts1 of
    TSym "<"  : r -> Right (RLt, r)
    TSym "<=" : r -> Right (RLe, r)
    TSym "="  : r -> Right (REq, r)
    _ -> expected "'<', '<=' or '='" ts1
  (m, ts3) <- exprJ ts2
  Right (RCs l rel m, ts3)

------------------------------------------------------------------------
-- Expressions

expr :: P R
expr ts
  | isSym "\\" ts = do
      ((), r1) <- sym "\\" ts
      (xs, r2) <- many1 ident r1
      ((), r3) <- sym "->" r2
      (b, r4)  <- expr r3
      Right (RLam xs b, r4)
  | isSym "<" ts = do
      ((), r1) <- sym "<" ts
      (xs, r2) <- many1 ident r1
      ((), r3) <- sym ">" r2
      (b, r4)  <- expr r3
      Right (RLLam xs b, r4)
  | isSym "[" ts = case levelBinders ts of
      Right (xs, r1) -> do (b, r2) <- expr r1
                           Right (RLPi xs b, r2)
      Left _ -> do
        ((), r1) <- sym "[" ts
        (cs, r2) <- constraints r1
        ((), r3) <- sym "]" r2
        (b, r4)  <- expr r3
        Right (RCPi cs b, r4)
  | otherwise = case telescope ts of
      Right (tel@(_ : _), ts1)
        | isSym "->" ts1 -> do ((), ts2) <- sym "->" ts1
                               (b, ts3) <- expr ts2
                               Right (RPi tel b, ts3)
        | isSym "*" ts1  -> do ((), ts2) <- sym "*" ts1
                               (b, ts3) <- expr ts2
                               Right (RSig tel b, ts3)
      _ -> do
        (a, ts1) <- exprJ ts
        if isSym "->" ts1
          then do ((), ts2) <- sym "->" ts1
                  (b, ts3) <- expr ts2
                  Right (RArr a b, ts3)
          else if isSym "*" ts1
            then do ((), ts2) <- sym "*" ts1
                    (b, ts3) <- expr ts2
                    Right (RTimes a b, ts3)
            else Right (a, ts1)
 where
  levelBinders t0 = do
    ((), t1) <- sym "[" t0
    (xs, t2) <- many1 ident t1
    ((), t3) <- sym "]" t2
    Right (xs, t3)

-- level joins:  e \/ e \/ ..
exprJ :: P R
exprJ ts = do
  (a, ts1) <- expr1 ts
  go a ts1
 where
  go a t | isSym "\\/" t = do ((), t1) <- sym "\\/" t
                              (b, t2) <- expr1 t1
                              go (RMax a b) t2
         | otherwise = Right (a, t)

expr1 :: P R
expr1 ts = do
  (h, ts1) <- expr2 ts
  go h ts1
 where
  go h t
    | isSym "@" t = do ((), t1) <- sym "@" t
                       (l, t2) <- expr2 t1
                       go (RLApp h l) t2
    | isSym "{" t = do ((), t1) <- sym "{" t
                       (a, t2) <- expr t1
                       ((), t3) <- sym "}" t2
                       go (RApp h (RHid a)) t3
    | otherwise = case expr2 t of
        Right (a, t1) -> go (RApp h a) t1
        Left _        -> Right (h, t)

expr2 :: P R
expr2 ts = do
  (a, ts1) <- expr3 ts
  post a ts1
 where
  post a t = case t of
    TSym ".1" : r -> post (RFst a) r
    TSym ".2" : r -> post (RSnd a) r
    TProj l : r   -> post (RDot a l) r
    TSym "+" : r  -> post (RSuc a) r
    TSym "[" : _  -> do (as, r) <- args t
                        post (RInst a as) r
    _             -> Right (a, t)
  args t0 = do
    ((), t1) <- sym "[" t0
    if isSym "]" t1 then do ((), t2) <- sym "]" t1; Right ([], t2) else do
      (a, t2) <- arg t1
      (as, t3) <- manyP (\t -> do ((), t') <- sym "," t; arg t') t2
      ((), t4) <- sym "]" t3
      Right (a : as, t4)
  arg t0 = case t0 of
    TId x : TSym ":=" : t1 -> do (e, t2) <- expr t1; Right ((Just x, e), t2)
    _ -> do (e, t1) <- expr t0; Right ((Nothing, e), t1)

expr3 :: P R
expr3 ts = case ts of
  TId "U" : rest    -> do (l, r1) <- expr2 rest
                          Right (RU l, r1)
  TId "Id" : rest   -> do (a, r1) <- expr2 rest
                          (x, r2) <- expr2 r1
                          (y, r3) <- expr2 r2
                          Right (RId a x y, r3)
  TId "refl" : rest -> do (a, r1) <- expr2 rest
                          Right (RRefl a, r1)
  TId "_" : rest    -> Right (RHole, rest)
  TId "new" : rest  -> do (a, r1) <- expr2 rest
                          Right (RNew a, r1)
  TId "idJ" : rest  -> do (a, r1) <- expr2 rest
                          (x, r2) <- expr2 r1
                          (c, r3) <- expr2 r2
                          (d, r4) <- expr2 r3
                          (y, r5) <- expr2 r4
                          (p, r6) <- expr2 r5
                          Right (RIdJ a x c d y p, r6)
  TId "calc" : rest -> do (a, r1) <- expr2 rest
                          ((), r2) <- sym "{" r1
                          (x0, r3) <- expr r2
                          (steps, r4) <- many1 calcStep r3
                          ((), r5) <- sym "}" r4
                          Right (calcChain a x0 steps, r5)
  TId "let" : rest  -> do ((), r1) <- sym "{" rest
                          (us, r2) <- units r1
                          ((), r3) <- sym "}" r2
                          ((), r4) <- kw "in" r3
                          (b, r5)  <- expr r4
                          Right (RLet us b, r5)
  TId "split" : rest -> do ((), r1) <- sym "{" rest
                           (bs, r2) <- branches r1
                           ((), r3) <- sym "}" r2
                           Right (RSplit (occ ts) bs, r3)
  TId "sig" : rest  -> do ((), r1) <- sym "{" rest
                          (fs, r2) <- fields ":" r1
                          ((), r3) <- sym "}" r2
                          Right (RRec fs, r3)
  TId "struct" : rest -> do ((), r1) <- sym "{" rest
                            (fs, r2) <- fields "=" r1
                            ((), r3) <- sym "}" r2
                            Right (RStruct fs, r3)
  TSym "(" : rest   -> do (e, r1)  <- expr rest
                          (es, r2) <- manyP (\t -> do ((), t') <- sym "," t; expr t') r1
                          ((), r3) <- sym ")" r2
                          Right (if null es then e else RTuple (e : es), r3)
  _                 -> do (x, r1) <- ident ts
                          Right (RVar x, r1)

-- An equational chain  calc A { a0 =< p1 > a1 =< p2 > a2 .. }:  every point
-- written once, desugared to Prelude's trans (J on the second path), right
-- nested as  trans p1 (trans p2 ..).  Each step is checked locally:  pi
-- against  Id A a(i-1) ai .  The motive's binders cannot be written by the
-- user ('%' is not an identifier character), so they capture nothing.
calcStep :: P (R, R)
calcStep ts = do
  ((), r1) <- sym "=" ts
  ((), r2) <- sym "<" r1
  (p, r3)  <- expr r2
  ((), r4) <- sym ">" r3
  (y, r5)  <- expr r4
  Right ((p, y), r5)

calcChain :: R -> R -> [(R, R)] -> R
calcChain a x steps = case steps of
  [(p, y)] -> RIdJ a x (RLam ["%w", "%r"] (RId a x (RVar "%w"))) (RRefl x) y p
  _        -> go x steps
 where
  go _ []               = error "calcChain"
  go _ [(p, _)]         = p
  go x0 ((p, y) : rest) =
    RIdJ a y (RLam ["%w", "%r"] (RId a x0 (RVar "%w"))) p (lastPt rest) (go y rest)
  lastPt = snd . last

fields :: String -> P [(Name, R)]
fields sep ts
  | isSym "}" ts = Right ([], ts)
  | otherwise = do
      (l, r1) <- ident ts
      ((), r2) <- sym sep r1
      (a, r3) <- expr r2
      if isSym ";" r3
        then do ((), r4) <- sym ";" r3
                (fs, r5) <- fields sep r4
                Right ((l, a) : fs, r5)
        else Right ([(l, a)], r3)

branches :: P [(Name, [Name], RBody)]
branches ts
  | isSym "}" ts = Right ([], ts)
  | otherwise = do
      (c, r1)  <- ident ts
      (xs, r2) <- manyP ident r1
      ((), r3) <- sym "->" r2
      (e, r4)  <- body r3
      if isSym ";" r4
        then do ((), r5) <- sym ";" r4
                (bs, r6) <- branches r5
                Right ((c, xs, e) : bs, r6)
        else Right ([(c, xs, e)], r4)

body :: P RBody
body ts0 = do
  (e, ts1) <- expr ts0
  if isKw "where" ts1
    then do ((), r1) <- kw "where" ts1
            ((), r2) <- sym "{" r1
            (us, r3) <- units r2
            ((), r4) <- sym "}" r3
            Right (RBody e us, r4)
    else Right (RBody e [], ts1)

------------------------------------------------------------------------
-- Units

endUnit :: [Tok] -> Either String [Tok]
endUnit ts
  | isSym ";" ts            = fmap snd (sym ";" ts)
  | null ts || isSym "}" ts = Right ts
  | otherwise               = expected "';'" ts

units :: P [RUnit]
units ts
  | null ts || isSym "}" ts = Right ([], ts)
  | otherwise = do
      (u, r1) <- unit ts
      r2 <- endUnit r1
      (us, r3) <- units r2
      Right (u : us, r3)

unit :: P RUnit
unit ts
  | isSym "#" ts = do
      ((), r1) <- sym "#" ts
      case r1 of
        TId "normal" : r2 -> do (e, r3) <- expr r2; Right (RNormal e, r3)
        TId "type" : r2   -> do (e, r3) <- expr r2; Right (RType e, r3)
        TId "conv" : r2   -> do (a, r3) <- expr r2
                                ((), r4) <- sym "=" r3
                                (b, r5) <- expr r4
                                Right (RConv a b, r5)
        TId "fails" : r2  -> do ((), r3) <- sym "{" r2
                                (us, r4) <- units r3
                                ((), r5) <- sym "}" r4
                                Right (RFails us, r5)
        _ -> expected "normal, type, conv or fails" r1
  | isKw "level" ts = do ((), r1) <- kw "level" ts
                         (xs, r2) <- many1 ident r1
                         Right (RLevel xs, r2)
  | isKw "constraint" ts = do ((), r1) <- kw "constraint" ts
                              (cs, r2) <- constraints r1
                              Right (RCstr cs, r2)
  | isKw "opaque" ts = do ((), r1) <- kw "opaque" ts
                          (e, r2) <- expr2 r1
                          Right (ROpaque e, r2)
  | isKw "transparent" ts = do ((), r1) <- kw "transparent" ts
                               (e, r2) <- expr2 r1
                               Right (RTransparent e, r2)
  | isKw "transparent_all" ts = do ((), r1) <- kw "transparent_all" ts
                                   Right (RTransAll, r1)
  | isKw "open" ts = do ((), r1) <- kw "open" ts
                        (e, r2) <- expr2 r1
                        Right (ROpen (occ ts) e, r2)
  | isKw "import" ts = do ((), r1) <- kw "import" ts
                          (x, r2) <- ident r1
                          Right (RImport x, r2)
  | isKw "module" ts = do
      ((), r1) <- kw "module" ts
      (x, r2) <- ident r1
      if isSym "=" r2
        then do ((), r3) <- sym "=" r2
                (e, r4) <- expr2 r3
                Right (RModInst x e, r4)
        else do (tel, r3) <- telescope r2
                ((), r4) <- sym "{" r3
                (us, r5) <- units r4
                ((), r6) <- sym "}" r5
                Right (RModule x tel us, r6)
  | isKw "data" ts = do
      ((), r1)  <- kw "data" ts
      (x, r2)   <- ident r1
      (tel, r3) <- telescope r2
      (ty, r4)  <- if isSym ":" r3
                     then do ((), r) <- sym ":" r3
                             (a, r') <- expr r
                             Right (Just a, r')
                     else Right (Nothing, r3)
      ((), r5)  <- sym "=" r4
      (ls, r6)  <- labels r5
      Right (RData (occ ts) x tel ty ls, r6)
  | otherwise = do
      (x, r1)   <- ident ts
      (tel, r2) <- telescope r1
      ((), r3)  <- sym ":" r2
      (a, r4)   <- expr r3
      if isSym "=" r4
        then do ((), r5) <- sym "=" r4
                (b, r6)  <- body r5
                Right (RDef (occ ts) x tel a (Just b), r6)
        else Right (RDef (occ ts) x tel a Nothing, r4)

labels :: P [(Name, [TItem])]
labels ts
  | isSym ";" ts || isSym "}" ts || null ts = Right ([], ts)
labels ts = do
  (c, r1)   <- ident ts
  (tel, r2) <- telescope r1
  if isSym "|" r2
    then do ((), r3) <- sym "|" r2
            (ls, r4) <- labels r3
            Right ((c, tel) : ls, r4)
    else Right ([(c, tel)], r2)

parseUnits :: String -> Either String [RUnit]
parseUnits src = do
  ts <- lexer src
  (us, rest) <- units ts
  if null rest then Right us else expected "a unit" rest

------------------------------------------------------------------------
-- Resolution
--
-- A scope maps a short name to what it denotes.  The labels of all sums
-- form one table (a constructor is only ever CHECKED against a sum, so
-- labels need no qualification).

data PKind = PTm | PLv deriving (Eq, Show)

-- the positions of a declaration's header telescope: explicit, hidden,
-- level.  Hiddenness belongs to the DECLARATION (the Agda-wiki design):
-- {x : A} -> B is (x : A) -> B, and only uses of the name are read with
-- a hole at each hidden position.
data Pos = PE | PH | PL deriving (Eq, Show)

telMask :: [TItem] -> [Pos]
telMask = concatMap m
 where m t = case t of
         TVars xs _  -> map (const PE) xs
         TVarsH xs _ -> map (const PH) xs
         TLvls xs    -> map (const PL) xs
         TCs _       -> []

data ModInfo = ModInfo
  { miParams  :: [(Name, PKind)]
  , miMembers :: [(Name, Maybe ModInfo)]    -- a term member, or a submodule
  , miPath    :: String
  , miMasks   :: [(Name, [Pos])] }
  deriving (Show)

data SInfo
  = SVar                       -- lambda/pattern variable, parameter, PN
  | SLvl
  | SDef Id
  | SMod ModInfo
  | SVarS ModInfo              -- a variable whose type is a segment
  | SField Name                -- a member of the opened variable c: c.x
  | SOpen MExp String (Maybe ModInfo) -- a member of an opened module (its path)
  deriving (Show)

type Scope = [(Name, SInfo)]

data RS = RS { rsScope :: Scope, rsLabels :: [(Name, Int)], rsPath :: String
             , rsLocks :: [Id], rsMasks :: [(Name, [Pos])]
             -- Map mirrors of rsScope / rsMasks for lookups (the lists keep
             -- the order, which open and the label positions need)
             , rsScopeM :: M.Map Name SInfo, rsMasksM :: M.Map Name [Pos] }

look :: RS -> Name -> Maybe SInfo
look rs x = M.lookup x (rsScopeM rs)

-- the first binding of a name in xs wins, as with lookup on xs ++ scope
bindS :: RS -> [(Name, SInfo)] -> RS
bindS rs xs = rs { rsScope = xs ++ rsScope rs
                 , rsMasks = [ (x, []) | (x, _) <- xs ] ++ rsMasks rs
                 , rsScopeM = M.union (M.fromList (reverse xs)) (rsScopeM rs)
                 , rsMasksM = M.union (M.fromList [ (x, []) | (x, _) <- xs ]) (rsMasksM rs) }

withMasks :: RS -> [(Name, [Pos])] -> RS
withMasks rs ms = rs { rsMasks = ms' ++ rsMasks rs
                     , rsMasksM = M.union (M.fromList (reverse ms')) (rsMasksM rs) }
 where ms' = [ m | m@(_, ps) <- ms, PH `elem` ps ]

type Rz a = Either String a

-- level expressions
resLv :: RS -> R -> Rz Lv
resLv rs r = case r of
  RVar x -> case look rs x of
    Just SLvl -> Right (LV x)
    _ -> Left ("not a level variable: " ++ x)
  RSuc a   -> fmap LSuc (resLv rs a)
  RMax a b -> do a' <- resLv rs a; b' <- resLv rs b; Right (LMax a' b')
  _ -> Left ("not a level: " ++ show r)

resCs :: RS -> RCs -> Rz Cs
resCs rs (RCs l rel m) = do l' <- resLv rs l; m' <- resLv rs m; Right (Cs l' rel m')

-- telescopes: returns the binders (for the Pi/Lam) and the scope inside
data Bind = BVar Name Exp | BLvl Name | BCs [Cs]

resTel :: RS -> [TItem] -> Rz ([Bind], RS)
resTel rs [] = Right ([], rs)
resTel rs (t : ts) = case t of
  TVars xs a -> do
    a' <- resE rs a
    (bs, rs') <- resTel (bindS rs [ (x, varInfo rs a) | x <- xs ]) ts
    Right ([ BVar x a' | x <- xs ] ++ bs, rs')
  TVarsH xs a -> resTel rs (TVars xs a : ts)
  TLvls xs -> do
    (bs, rs') <- resTel (bindS rs [ (x, SLvl) | x <- xs ]) ts
    Right (map BLvl xs ++ bs, rs')
  TCs cs -> do
    cs' <- mapM (resCs rs) cs
    (bs, rs') <- resTel rs ts
    Right (BCs cs' : bs, rs')

piB :: [Bind] -> Exp -> Exp
piB bs b = foldr f b bs
 where f (BVar x a) e = Pi x a e
       f (BLvl x) e   = LPi x e
       f (BCs cs) e   = CPi cs e

lamB :: [Bind] -> Exp -> Exp
lamB bs b = foldr f b bs
 where f (BVar x _) e = Lam x e
       f (BLvl x) e   = LLam x e
       f (BCs _) e    = e

-- a variable of segment type remembers the segment, for  open c
varInfo :: RS -> R -> SInfo
varInfo rs a = case segInfo a of
  Just mi -> SVarS mi
  Nothing -> SVar
 where
  segInfo r = case r of
    RVar _   -> either (const Nothing) (Just . snd) (resM rs r)
    RDot _ _ -> either (const Nothing) (Just . snd) (resM rs r)
    RInst h _ -> segInfo h
    _ -> Nothing

-- module expressions
resM :: RS -> R -> Rz (MExp, ModInfo)
resM rs r = case r of
  RVar x -> case look rs x of
    Just (SMod mi)           -> Right (MVar x, mi)
    Just (SOpen m _ (Just mi)) -> Right (MSub m x, mi)
    _ -> Left ("not a module: " ++ x)
  RDot a x -> do
    (m, mi) <- resM rs a
    if not (null (miParams mi)) then Left ("module " ++ miPath mi ++ " needs arguments") else
      case lookup x (miMembers mi) of
        Just (Just mi') -> Right (MSub m x, mi')
        _ -> Left ("no submodule " ++ x ++ " in " ++ miPath mi)
  RInst a as -> do
    (m, mi) <- resM rs a
    fs <- resArgs rs mi as
    let ps = miParams mi
    case [ x | (x, _) <- ps, x `notElem` map fst fs ] of
      [] -> Right (MApp m [ a' | (x, _) <- ps, Just a' <- [lookup x fs] ], mi { miParams = [] })
      missing -> Left ("module " ++ miPath mi ++ ": no argument for " ++ unwords missing)
  _ -> Left ("not a module expression: " ++ show r)

-- arguments, positional then named: positional ones fill the parameters in
-- order (Arend: the first unimplemented fields), named ones by name
resArgs :: RS -> ModInfo -> [(Maybe Name, R)] -> Rz [(Name, Arg)]
resArgs rs mi as = do
  let ps = miParams mi
      (pos, named) = span ((== Nothing) . fst) as
  if length pos > length ps then Left ("module " ++ miPath mi ++ ": too many arguments") else do
    let posNamed = zip (map fst ps) (map snd pos)
    named' <- mapM (\(n, e) -> case n of
                      Just x  -> Right (x, e)
                      Nothing -> Left "positional argument after a named one") named
    let all' = posNamed ++ named'
    dupCheck (map fst all')
    mapM (\(x, e) -> case lookup x ps of
             Just PTm -> fmap (\e' -> (x, ATm e')) (resE rs e)
             Just PLv -> fmap (\l -> (x, ALv l)) (resLv rs e)
             Nothing  -> Left ("module " ++ miPath mi ++ " has no parameter " ++ x)) all'

-- a segment head (no arguments): for a type  M[x := e]
resHead :: RS -> R -> Rz (MExp, ModInfo)
resHead rs r = case r of
  RVar _ -> resM rs r
  RDot _ _ -> resM rs r
  _ -> Left "not a segment"

isModExp :: RS -> R -> Bool
isModExp rs r = case resM rs r of
  Right _ -> True
  Left _  -> False

resE :: RS -> R -> Rz Exp
resE rs r
  | (h, as) <- spineL r [], not (null as) || isHead h
  , ps <- headMask rs h, PH `elem` ps || any isHid as = do
      h' <- resE0 rs h
      insertHoles rs h' ps as
resE rs r = resE0 rs r

isHead :: R -> Bool
isHead r = case r of
  RVar _   -> True
  RDot _ _ -> True
  _        -> False

isHid :: Either R R -> Bool
isHid (Left (RHid _)) = True
isHid _ = False

-- a spine with term (Left) and level (Right) arguments
spineL :: R -> [Either R R] -> (R, [Either R R])
spineL r as = case r of
  RApp a b  -> spineL a (Left b : as)
  RLApp a l -> spineL a (Right l : as)
  _         -> (r, as)

-- the mask of the head of an application, if it is a declared name
headMask :: RS -> R -> [Pos]
headMask rs h = case h of
  RVar x -> maybe [] id (M.lookup x (rsMasksM rs))
  RDot a l
    | Right (_, mi) <- resM rs a -> maybe [] id (lookup l (miMasks mi))
    | RVar c <- a, Just (SVarS mi) <- look rs c -> maybe [] id (lookup l (miMasks mi))
  _ -> []

-- a hole at each hidden position, or the given {e}; after the last given
-- argument, the hidden positions that follow immediately get holes too
insertHoles :: RS -> Exp -> [Pos] -> [Either R R] -> Rz Exp
insertHoles rs = go
 where
  go acc (PH : ps) (Left (RHid e) : as) = do e' <- resE rs e; go (App acc e') ps as
  go acc (PH : ps) as = go (App acc Hole) ps as
  go acc (PE : ps) (Left e : as) = do
    e' <- plain e
    go (App acc e') ps as
  go acc (PL : ps) (Right l : as) = do l' <- resLv rs l; go (LApp acc l') ps as
  go acc [] as = foldl (\m a -> do
                          acc' <- m
                          case a of
                            Left e  -> fmap (App acc') (plain e)
                            Right l -> fmap (LApp acc') (resLv rs l)) (Right acc) as
  go acc _ [] = Right acc
  go _ (PL : _) (Left _ : _) = Left "a level argument (@l) is expected here"
  go _ (PE : _) (Right _ : _) = Left "a term argument is expected here, not a level"
  plain e = case e of
    RHid _ -> Left "a hidden argument {..} where the declaration has an explicit one"
    _      -> resE rs e

resE0 :: RS -> R -> Rz Exp
resE0 rs r = case spine r [] of
  (RVar x, as)
    | Nothing <- look rs x, (x, length as) `elem` rsLabels rs ->
        fmap (Con x) (mapM (resE rs) as)
  _ -> case r of
    RVar x -> case look rs x of
      Just SVar -> Right (Var x)
      Just (SDef _) -> Right (Var x)
      Just SLvl -> Left ("level variable used as a term: " ++ x)
      Just (SVarS _) -> Right (Var x)
      Just (SField c) -> Right (Proj (Var c) x)
      Just (SMod _) -> Right (SegT (MVar x) [])          -- the segment as a type
      Just (SOpen m _ Nothing) -> Right (Acc m x)
      Just (SOpen m _ (Just _)) -> Right (SegT (MSub m x) [])
      Nothing
        | (x, 0) `elem` rsLabels rs -> Right (Con x [])
        | any ((== x) . fst) (rsLabels rs) -> Left ("constructor " ++ x ++ " applied to the wrong number of arguments")
        | otherwise -> Left ("not in scope: " ++ x)
    RU l -> fmap U (resLv rs l)
    RApp a b -> do a' <- resE rs a; b' <- resE rs b; Right (App a' b')
    RLApp a l -> do a' <- resE rs a; l' <- resLv rs l; Right (LApp a' l')
    RLam xs b -> do b' <- resE (bindS rs [ (x, SVar) | x <- xs ]) b
                    Right (foldr Lam b' xs)
    RLLam xs b -> do b' <- resE (bindS rs [ (x, SLvl) | x <- xs ]) b
                     Right (foldr LLam b' xs)
    RLPi xs b -> do b' <- resE (bindS rs [ (x, SLvl) | x <- xs ]) b
                    Right (foldr LPi b' xs)
    RCPi cs b -> do cs' <- mapM (resCs rs) cs
                    b' <- resE rs b
                    Right (CPi cs' b')
    RPi tel b -> do (bs, rs') <- resTel rs tel
                    b' <- resE rs' b
                    Right (piB bs b')
    RArr a b -> do a' <- resE rs a; b' <- resE rs b; Right (Pi "_" a' b')
    RSig tel b -> do
      (bs, rs') <- resTel rs tel
      b' <- resE rs' b
      e' <- foldr (\bd acc -> case bd of
                BVar x a -> fmap (Sig x a) acc
                _ -> Left "only term binders in a Sigma") (Right b') bs
      Right e'                      -- (x : A) * B : compared structurally
    RTimes a b -> do a' <- resE rs a; b' <- resE rs b; Right (Sig "_" a' b')
    RLet us b -> do (us', rs') <- resLocal rs us
                    b' <- resE rs' b
                    Right (Let us' b')
    RTuple es -> do es' <- mapM (resE rs) es
                    Right (foldr1 Pair es')
    RFst a -> fmap Fst (resE rs a)
    RSnd a -> fmap Snd (resE rs a)
    RDot a l
      | isModExp rs a -> do
          (m, mi) <- resM rs a
          if not (null (miParams mi)) then Left ("module " ++ miPath mi ++ " needs arguments") else
            case lookup l (miMembers mi) of
              Just Nothing -> Right (Acc m l)
              Just (Just _) -> Right (SegT (MSub m l) [])
              Nothing -> Left ("no member " ++ l ++ " in module " ++ miPath mi)
      | otherwise -> do
          a' <- resE rs a
          -- on a variable a member already unfolds (the variable is bound
          -- to its eta-expansion); otherwise the filling pass decides
          -- a FIELD of a variable is a projection; a defined MEMBER of a
          -- variable of segment type is resolved by eta in the filling
          -- pass, since the variable may be instantiated by a neutral
          Right (case (a, a') of
            (RVar c, Var _) -> case look rs c of
              Just (SVarS mi) | l `notElem` map fst (miParams mi) -> ProjU a' l
              Just (SDef _) -> ProjU a' l      -- a defined element: s = b.bs l
              _ -> Proj a' l
            (_, Var _) -> Proj a' l
            _ -> ProjU a' l)
    RInst a as -> do
      (m, mi) <- resHead rs a
      fs <- resArgs rs mi as
      Right (SegT m fs)
    RNew a -> do
      (m, mi) <- resM rs a
      if not (null (miParams mi)) then Left ("new " ++ miPath mi ++ ": arguments missing")
        else Right (named rs (New m))
    RSplit o bs -> do
      bs' <- mapM (\(c, xs, b) -> do b' <- resBody (bindS rs [ (x, SVar) | x <- xs ]) b
                                     Right (c, (xs, b'))) bs
      Right (Split (rsPath rs ++ "split#" ++ show o) [] bs')
    RRec fs -> do fs' <- resFields rs fs
                  Right (named rs (Rec fs'))
    RStruct fs -> fmap (named rs . Struct) (mapM (\(l, e) -> do e' <- resE rs e; Right (l, e')) fs)
    RId a x y -> do a' <- resE rs a; x' <- resE rs x; y' <- resE rs y; Right (Id a' x' y')
    RRefl a -> fmap Refl (resE rs a)
    RIdJ a x c d y p -> do
      es <- mapM (resE rs) [a, x, c, d, y, p]
      let [a', x', c', d', y', p'] = es
      Right (IdJ a' x' c' d' y' p')
    RHid _ -> Left "a hidden argument {..} applied to a name without hidden parameters"
    RHole -> Right Hole
    RSuc _ -> Left "a level used as a term"
    RMax _ _ -> Left "a level used as a term"
 where
  spine (RApp a b) as = spine a (b : as)
  spine h as          = (h, as)

-- the internal name of a sig occurrence (Half/Gofer): its text.
-- The same text is the same name; together with the values of the
-- variables it depends on (added by the annotator) it identifies the type
named :: RS -> Exp -> Exp
named _ e = Named ("sig#" ++ show (textHash (show e))) [] e

-- the free names of an expression, in order of occurrence
freeVarsT :: Exp -> [Name]
freeVarsT e0 = go [] e0
 where
  go bs e = case e of
    Var x        -> [ x | x `notElem` bs ]
    App a b      -> go bs a ++ go bs b
    Lam x b      -> go (x : bs) b
    Pi x a b     -> go bs a ++ go (x : bs) b
    Sig x a b    -> go bs a ++ go (x : bs) b
    Named _ _ a  -> go bs a
    Pair a b     -> go bs a ++ go bs b
    Fst a        -> go bs a
    Snd a        -> go bs a
    Proj a _     -> go bs a
    ProjU a _    -> go bs a
    Rec t        -> tel bs t
    Id a x y     -> go bs a ++ go bs x ++ go bs y
    Refl a       -> go bs a
    Con _ as     -> concatMap (go bs) as
    LApp a l     -> go bs a ++ lvs bs l
    U l          -> lvs bs l
    Struct fs    -> concatMap (go bs . snd) fs
    New m        -> me bs m
    Acc m _      -> me bs m
    SegT m fs    -> me bs m ++ concat [ ar bs a | (_, a) <- fs ]
    Let us b     -> let bs' = [ unitName u | u <- us ] ++ bs
                    in concat [ go bs' a ++ go bs' t | UDef _ _ a t _ <- us ] ++ go bs' b
    Split _ _ br -> concat [ go (xs ++ bs) b | (_, (xs, b)) <- br ]
    _            -> []
  me bs m = case m of
    MVar _    -> []
    MSub n _  -> me bs n
    MApp n as -> me bs n ++ concatMap (ar bs) as
  ar bs (ATm a) = go bs a
  ar bs (ALv l) = lvs bs l
  tel _ [] = []
  tel bs ((x, a) : t) = go bs a ++ tel (x : bs) t
  lvs bs l = case l of
    LV x -> [ x | x `notElem` bs ]
    LSuc m -> lvs bs m
    LMax a b -> lvs bs a ++ lvs bs b
    LZero -> []

-- rename free variables (bound names are left alone)
renameFree :: [(Name, Name)] -> Exp -> Exp
renameFree m0 e0 = go m0 e0
 where
  go m e = case e of
    Var x        -> Var (maybe x id (lookup x m))
    App a b      -> App (go m a) (go m b)
    Lam x b      -> Lam x (go (drop' x m) b)
    Pi x a b     -> Pi x (go m a) (go (drop' x m) b)
    Sig x a b    -> Sig x (go m a) (go (drop' x m) b)
    Named i d a  -> Named i d (go m a)
    Pair a b     -> Pair (go m a) (go m b)
    Fst a        -> Fst (go m a)
    Snd a        -> Snd (go m a)
    Proj a l     -> Proj (go m a) l
    ProjU a l    -> ProjU (go m a) l
    Rec t        -> Rec (tel m t)
    Id a x y     -> Id (go m a) (go m x) (go m y)
    Refl a       -> Refl (go m a)
    Con c as     -> Con c (map (go m) as)
    LApp a l     -> LApp (go m a) (lv m l)
    U l          -> U (lv m l)
    Struct fs    -> Struct [ (l, go m a) | (l, a) <- fs ]
    New me       -> New (mx m me)
    Acc me x     -> Acc (mx m me) x
    SegT me fs   -> SegT (mx m me) [ (x, ar m a) | (x, a) <- fs ]
    _            -> e
  mx m me = case me of
    MVar x    -> MVar x
    MSub n x  -> MSub (mx m n) x
    MApp n as -> MApp (mx m n) (map (ar m) as)
  ar m (ATm a) = ATm (go m a)
  ar m (ALv l) = ALv (lv m l)
  drop' x = filter ((/= x) . fst)
  tel _ [] = []
  tel m ((x, a) : t) = (x, go m a) : tel (drop' x m) t
  lv m l = case l of
    LV x -> LV (maybe x id (lookup x m))
    LSuc a -> LSuc (lv m a)
    LMax a b -> LMax (lv m a) (lv m b)
    LZero -> LZero

textHash :: String -> Int
textHash = foldl (\h c -> (h * 33 + fromEnum c) `mod` 1000000007) 5381

resFields :: RS -> [(Name, R)] -> Rz Tel
resFields _ [] = Right []
resFields rs ((l, a) : fs) = do
  a' <- resE rs a
  fs' <- resFields (bindS rs [(l, SVar)]) fs
  Right ((l, a') : fs')

resBody :: RS -> RBody -> Rz Exp
resBody rs (RBody e []) = resE rs e
resBody rs (RBody e us) = do
  (us', rs') <- resLocal rs us
  e' <- resE rs' e
  Right (Let us' e')

-- a let / where block: definitions only, one mutual group
resLocal :: RS -> [RUnit] -> Rz ([Unit], RS)
resLocal rs us = do
  let names = [ x | RDef _ x _ _ _ <- us ] ++ [ x | RData _ x _ _ _ <- us ]
  if length us /= length names then Left "only definitions may appear in a let or where block" else do
    let rs' = (withMasks (bindS rs [ (x, SDef x) | x <- names ])
                         [ (x, telMask tel) | RDef _ x tel _ _ <- us ])
                { rsLabels = rsLabels rs ++ labelsOf us }
    us' <- mapM (resDef rs' True) us
    Right (us', rs')

resDef :: RS -> Bool -> RUnit -> Rz Unit
resDef rs local u = either (\m -> Left ("in " ++ rsPath rs ++ unitNm u ++ ": " ++ m)) Right (resDef' rs local u)

unitNm :: RUnit -> String
unitNm u = case u of
  RDef _ x _ _ _ -> x
  RData _ x _ _ _ -> x
  _ -> "?"

resDef' :: RS -> Bool -> RUnit -> Rz Unit
resDef' rs local u = case u of
  RDef o x tel a mb -> do
    (bs, rs1) <- resTel rs tel
    a' <- resE rs1 a
    let i = idOf x o
    case mb of
      Nothing -> Left ("a definition without a body in a let: " ++ x)
      Just b -> do
        b' <- resBody rs1 { rsPath = i ++ "/" } b
        Right (UDef i x (piB bs a') (lamB bs (nameSplit i b')) [])
  RData o x tel ty ls -> do
    (bs, rs1) <- resTel rs tel
    ty' <- case ty of
      Nothing -> Right (U LZero)
      Just t  -> resE rs1 t
    ls' <- mapM (\(c, ctel) -> do (cbs, _) <- resTel rs1 ctel
                                  tel' <- mapM (\bd -> case bd of
                                                  BVar y a -> Right (y, a)
                                                  _ -> Left "only term binders in a constructor") cbs
                                  Right (c, tel')) ls
    let i = idOf x o
    Right (UDef i x (piB bs ty') (lamB bs (Sum i [] ls')) [])
  _ -> Left "not a definition"
 where
  idOf x o = rsPath rs ++ x ++ (if local then "#" ++ show o else "")
  -- a split that is the body of a definition is named after it
  nameSplit i e = case e of
    Split _ ds bs -> Split i ds bs
    Let us b      -> Let us (nameSplit i b)
    _             -> e

labelsOf :: [RUnit] -> [(Name, Int)]
labelsOf us = concat [ [ (c, sum (map width tel)) | (c, tel) <- ls ] | RData _ _ _ _ ls <- us ]
 where width (TVars xs _) = length xs
       width _ = 0

-- all labels in a program, modules and where blocks included
allLabels :: [RUnit] -> [(Name, Int)]
allLabels = concatMap go
 where
  go u = case u of
    RData{} -> labelsOf [u]
    RDef _ _ _ _ (Just (RBody e ws)) -> allLabels ws ++ inR e
    RModule _ _ us -> allLabels us
    RFails us -> allLabels us
    _ -> []
  inR e = case e of
    RLet us b -> allLabels us ++ inR b
    RSplit _ bs -> concat [ allLabels ws ++ inR b | (_, _, RBody b ws) <- bs ]
    RLam _ b -> inR b
    RApp a b -> inR a ++ inR b
    _ -> []

-- The units of a module body or of the program, in order.  Consecutive
-- definitions form one mutual group.
resUnits :: RS -> [RUnit] -> Int -> Rz ([Unit], RS)
resUnits rs [] _ = Right ([], rs)
resUnits rs (u : us) n = case u of
  RLevel xs -> do
    mapM_ (fresh rs) xs
    (us', rs') <- resUnits (bindS rs [ (x, SLvl) | x <- xs ]) us n
    Right (map ULvl xs ++ us', rs')
  RCstr cs -> do
    cs' <- mapM (resCs rs) cs
    (us', rs') <- resUnits rs us n
    Right (UCstr cs' : us', rs')
  RDef _ x tel a Nothing -> do
    fresh rs x
    (bs, rs1) <- resTel rs tel
    a' <- resE rs1 a
    (us', rs') <- resUnits (withMasks (bindS rs [(x, if null tel then varInfo rs a else SVar)])
                                      [(x, telMask tel)]) us n
    Right (UPar (rsPath rs ++ x) x (piB bs a') : us', rs')
  RModule x tel body -> do
    fresh rs x
    let rsIn = rs { rsPath = rsPath rs ++ x ++ "." }
    (bs, rsTel) <- resTel rsIn tel
    let varOf y = maybe SVar id (M.lookup y (rsScopeM rsTel))
    let headUnits = map bindUnit bs
        bindUnit bd = case bd of
          BVar y a -> UPar (rsPath rsIn ++ y) y a
          BLvl y   -> ULvl y
          BCs cs   -> UCstr cs
        rsHead = bindS rsIn (concatMap bindScope bs)
        bindScope bd = case bd of
          BVar y _ -> [(y, varOf y)]
          BLvl y   -> [(y, SLvl)]
          BCs _    -> []
    (bodyUnits, rsBody) <- resUnits rsHead body 0
    let all' = headUnits ++ bodyUnits
        mi = ModInfo [ (unitName v, k) | v <- all', Just k <- [paramKind v] ]
                     (membersOf rsBody rsHead ++ [ (unitName v, Nothing) | v@(UPar{}) <- headUnits ])
                     (rsPath rs ++ x)
                     [ (y, ps) | (y, _) <- membersOf rsBody rsHead
                               , Just ps <- [M.lookup y (rsMasksM rsBody)], PH `elem` ps ]
    -- the lock strategy is global and positional: what the body set persists
    let rsAfter = (bindS rs [(x, SMod mi)]) { rsLocks = rsLocks rsBody }
        us2 = case recordCon x tel body of
          Just c@(RDef _ mk _ _ _)
            | mk `notElem` concatMap definedNames us
            , Right _ <- resUnits rsAfter [c] n -> c : us
          _ -> us
    (us', rs') <- resUnits rsAfter us2 n
    Right (UMod (rsPath rs ++ x) x all' [] : us', rs')
  RModInst x e -> do
    fresh rs x
    (m, mi) <- resM rs e
    if not (null (miParams mi)) then Left ("module " ++ miPath mi ++ " needs arguments") else do
      (us', rs') <- resUnits (bindS rs [(x, SMod mi)]) us n
      Right (UInst (rsPath rs ++ x) x m : us', rs')
  ROpen _ (RVar c) | Just (SVarS mi) <- look rs c -> do
    let opened = [ (y, SField c) | (y, Nothing) <- miMembers mi, not (M.member y (rsScopeM rs)) ]
    resUnits (withMasks (bindS rs opened) (miMasks mi)) us n
  ROpen o e -> do
    (m, mi) <- resM rs e
    if not (null (miParams mi)) then Left ("module " ++ miPath mi ++ " needs arguments") else do
      let (pre, m') = case m of
            -- unique in the whole program: o (the tokens left) is unique only
            -- within one file, and a nested open with the same name would
            -- shadow an enclosing one
            MApp _ _ -> let nm = "open#" ++ show o ++ "@" ++ map (\c -> if c == '.' then '/' else c) (rsPath rs)
                        in ([UInst (rsPath rs ++ nm) nm m], MVar nm)
            _ -> ([], m)
          opened = [ (y, SOpen m' (miPath mi) k) | (y, k) <- miMembers mi
                                                  , not (M.member y (rsScopeM rs)) ]
      (us', rs') <- resUnits (withMasks (bindS rs opened) (miMasks mi)) us n
      Right (pre ++ us', rs')
  RImport x -> Left ("import " ++ x ++ " was not expanded")
  ROpaque e -> lockCmd e (\i s -> i : filter (/= i) s)
  RTransparent e -> lockCmd e (\i s -> filter (/= i) s)
  RTransAll -> do
    (us', rs') <- resUnits rs { rsLocks = [] } us n
    Right (ULock [] : us', rs')
  RNormal e -> directive (fmap DNormal (resE rs e))
  RType e -> directive (fmap DType (resE rs e))
  RConv a b -> directive (do a' <- resE rs a; b' <- resE rs b; Right (DConv a' b'))
  RFails xs -> case resUnits rs xs n of
    Left msg -> directive (Right (DFails [UDir (DNormal (Var ("#resolution failed: " ++ msg)))]))
    Right (xs', _) -> directive (Right (DFails xs'))
  _ -> do
    -- a group of definitions (and data): mutually recursive
    let isDefU v = case v of
          RDef _ _ _ _ (Just _) -> True
          RData{} -> True
          _ -> False
        (g, rest) = span isDefU (u : us)
        names = [ x | RDef _ x _ _ _ <- g ] ++ [ x | RData _ x _ _ _ <- g ]
    mapM_ (fresh rs) names
    dupCheck names
    let rsG = withMasks (bindS rs [ (x, SDef (rsPath rs ++ x)) | x <- names ])
                        [ (x, telMask tel) | RDef _ x tel _ _ <- g ]
    g' <- mapM (resDef rsG False) g
    (us', rs') <- resUnits rsG rest n
    Right (g' ++ us', rs')
 where
  directive me = do
    d <- me
    (us', rs') <- resUnits rs us n
    Right (UDir d : us', rs')
  lockCmd e f = do
    i <- lockId rs e
    let s = f i (rsLocks rs)
    (us', rs') <- resUnits rs { rsLocks = s } us n
    Right (ULock s : us', rs')

-- The constructor of a record.  A segment whose body has fields (body-less
-- units) gets  mkM (params) (fields) : M[params] = new M[params, fields] ,
-- one occurrence of `new`, so the elements it builds are compared by name.
-- Not generated when the body has level or constraint units, when a field
-- has hidden binders (a variable cannot carry hiddenness), or when a field
-- type mentions a member defined in the body (the definition then does not
-- resolve), or when mkM is defined by the user in the same block.
recordCon :: Name -> [TItem] -> [RUnit] -> Maybe RUnit
recordCon x tel body
  | null fields = Nothing
  | any bad body = Nothing
  | otherwise = Just (RDef 0 ("mk" ++ x) (tel ++ map field fields) resTy
                           (Just (RBody (RNew (RInst (RVar x) (map pos (params ++ map fst fields)))) [])))
 where
  fields = [ (y, if null ftel then a else RPi ftel a) | RDef _ y ftel a Nothing <- body ]
  field (y, a) = TVars [y] a
  bad u = case u of
    RDef _ _ ftel _ Nothing -> or [ True | TVarsH _ _ <- ftel ]
    RLevel _ -> True
    RCstr _  -> True
    _        -> False
  params = concat [ case t of
                      TVars ys _  -> ys
                      TVarsH ys _ -> ys
                      TLvls ys    -> ys
                      TCs _       -> []
                  | t <- tel ]
  pos y = (Nothing, RVar y)
  resTy | null params = RVar x
        | otherwise   = RInst (RVar x) (map pos params)

definedNames :: RUnit -> [Name]
definedNames u = case u of
  RDef _ y _ _ _  -> [y]
  RData _ y _ _ _ -> [y]
  RModule y _ _   -> [y]
  RModInst y _    -> [y]
  _               -> []

-- the qualified id a lock refers to
lockId :: RS -> R -> Rz Id
lockId rs e = case e of
  RVar x -> case look rs x of
    Just (SDef i) -> Right i
    Just (SOpen _ p Nothing) -> Right (p ++ "." ++ x)
    _ -> Left ("opaque/transparent: not a definition: " ++ x)
  RDot a x -> do
    (m, mi) <- resM rs a
    case lookup x (miMembers mi) of
      Just Nothing -> Right (miPath mi ++ "." ++ x)
      _ -> Left ("opaque/transparent: no definition " ++ x ++ " in " ++ showM m)
  _ -> Left "opaque/transparent: expected a name"

paramKind :: Unit -> Maybe PKind
paramKind u = case u of
  UPar{} -> Just PTm
  ULvl _ -> Just PLv
  _      -> Nothing

-- the members a module body added to the scope
membersOf :: RS -> RS -> [(Name, Maybe ModInfo)]
membersOf after before =
  [ (x, k) | (x, s) <- take (length (rsScope after) - length (rsScope before)) (rsScope after)
           , Just k <- [memberKind s] ]
 where
  memberKind s = case s of
    SVar     -> Just Nothing
    SVarS _  -> Just Nothing
    SDef _   -> Just Nothing
    SMod mi  -> Just (Just mi)
    _        -> Nothing

fresh :: RS -> Name -> Rz ()
fresh rs x = case look rs x of
  Just (SOpen _ _ _) -> Right ()
  Just (SField _) -> Right ()
  Just _  -> Left ("the name " ++ x ++ " is already declared (no shadowing)")
  Nothing -> Right ()

dupCheck :: [Name] -> Rz ()
dupCheck [] = Right ()
dupCheck (x : xs)
  | x `elem` xs = Left ("the name " ++ x ++ " is declared twice")
  | otherwise   = dupCheck xs

------------------------------------------------------------------------
-- Dependencies.  Every definition, labelled sum and split is annotated
-- with the variables it depends on, directly or through definitions in
-- scope: its DYNAMIC part.  Variables (lambda-bound, pattern variables,
-- parameters, level variables) depend on themselves; a definition on the
-- dependencies of its type and body; a module on what its body depends on
-- minus its own parameters; an access  M[args].x  on M and the arguments.

type DS = [(Name, [Name])]

dsLook :: DS -> Name -> [Name]
dsLook ds x = maybe [] id (lookup x ds)

uni :: [[Name]] -> [Name]
uni = nub . concat

lvNames :: Lv -> [Name]
lvNames l = case l of
  LV x     -> [x]
  LSuc m   -> lvNames m
  LMax a b -> lvNames a ++ lvNames b
  LZero    -> []

bindVs :: DS -> [Name] -> DS
bindVs ds xs = [ (x, [x]) | x <- xs ] ++ ds

annE :: DS -> Exp -> ([Name], Exp)
annE ds e = case e of
  U l          -> (lvD l, e)
  Var x        -> (dsLook ds x, e)
  App a b      -> bin App a b
  Lam x b      -> under [x] (Lam x) b
  Pi x a b     -> let (da, a') = annE ds a
                      (db, b') = annE (bindVs ds [x]) b
                  in (uni [da, db \\ [x]], Pi x a' b')
  Sig x a b    -> let (da, a') = annE ds a
                      (db, b') = annE (bindVs ds [x]) b
                  in (uni [da, db \\ [x]], Sig x a' b')
  Let us b     -> let (us', ds', _) = annGroup ds us
                      (db, b') = annE ds' b
                  in (db, Let us' b')
  Sum t _ cs   -> let ann = [ (c, annTel ds tel) | (c, tel) <- cs ]
                      d   = uni [ fst a | (_, a) <- ann ]
                  in (d, Sum t d [ (c, snd a) | (c, a) <- ann ])
  Con c as     -> let r = map (annE ds) as in (uni (map fst r), Con c (map snd r))
  Split t _ bs -> let ann = [ (c, (xs, annE (bindVs ds xs) b)) | (c, (xs, b)) <- bs ]
                      d   = uni [ fst r \\ xs | (_, (xs, r)) <- ann ]
                  in (d, Split t d [ (c, (xs, snd r)) | (c, (xs, r)) <- ann ])
  Pair a b     -> bin Pair a b
  Fst a        -> one Fst a
  Snd a        -> one Snd a
  Rec tel      -> let (d, tel') = annTel ds tel in (d, Rec tel')
  Struct fs    -> let r = [ (l, annE ds a) | (l, a) <- fs ]
                  in (uni [ fst a | (_, a) <- r ], Struct [ (l, snd a) | (l, a) <- r ])
  Proj a l     -> one (\a' -> Proj a' l) a
  Id a x y     -> let r = map (annE ds) [a, x, y]
                  in (uni (map fst r), let [a', x', y'] = map snd r in Id a' x' y')
  Refl a       -> one Refl a
  IdJ a x c d y p -> let r = map (annE ds) [a, x, c, d, y, p]
                         [a', x', c', d', y', p'] = map snd r
                     in (uni (map fst r), IdJ a' x' c' d' y' p')
  LPi x a      -> under [x] (LPi x) a
  LLam x a     -> under [x] (LLam x) a
  LApp a l     -> let (d, a') = annE ds a in (uni [d, lvD l], LApp a' l)
  CPi cs a     -> let (d, a') = annE ds a
                  in (uni (d : [ lvD l ++ lvD m | Cs l _ m <- cs ]), CPi cs a')
  Acc m x      -> let (d, m') = annM ds m in (d, Acc m' x)
  SegT m fs    -> let (d, m') = annM ds m
                      r = [ (x, annArg ds a) | (x, a) <- fs ]
                  in (uni (d : [ fst a | (_, a) <- r ]), SegT m' [ (x, snd a) | (x, a) <- r ])
  New m        -> let (d, m') = annM ds m in (d, New m')
  Hole         -> ([], Hole)
  -- the internal name: the text with its free variables renamed $1..$n in
  -- order (the text of the lambda-lifted form), so that the same shape over
  -- different variable names is the same name; the values decide
  Named _ _ a  -> let (d, a') = annE ds a
                      fv = nub (freeVarsT a)
                      canon = show (renameFree (zip fv [ "$" ++ show k | k <- [1 :: Int ..] ]) a)
                  in (d, Named ("sig#" ++ show (textHash canon)) d a')
  ProjU a l    -> let (d, a') = annE ds a in (d, ProjU a' l)
 where
  lvD l = uni (map (dsLook ds) (lvNames l))
  bin f a b = let (da, a') = annE ds a
                  (db, b') = annE ds b
              in (uni [da, db], f a' b')
  one f a = let (d, a') = annE ds a in (d, f a')
  under xs f b = let (d, b') = annE (bindVs ds xs) b in (d \\ xs, f b')

annTel :: DS -> Tel -> ([Name], Tel)
annTel _ [] = ([], [])
annTel ds ((x, a) : tel) =
  let (da, a')   = annE ds a
      (dt, tel') = annTel (bindVs ds [x]) tel
  in (uni [da, dt \\ [x]], (x, a') : tel')

annM :: DS -> MExp -> ([Name], MExp)
annM ds m = case m of
  MVar x    -> (dsLook ds x, m)
  MSub n x  -> let (d, n') = annM ds n in (d, MSub n' x)
  MApp n as -> let (d, n') = annM ds n
                   r = map (annArg ds) as
               in (uni (d : map fst r), MApp n' (map snd r))

annArg :: DS -> Arg -> ([Name], Arg)
annArg ds (ATm e) = let (d, e') = annE ds e in (d, ATm e')
annArg ds (ALv l) = (uni (map (dsLook ds) (lvNames l)), ALv l)

-- a mutual group of definitions: the dependencies are the least fixpoint
annGroup :: DS -> [Unit] -> ([Unit], DS, [Name])
annGroup ds us = (us', dsF, uni (map snd deps))
 where
  names = [ x | UDef _ x _ _ _ <- us ]
  dsT   = bindVs ds names
  raw   = [ (x, uni [fst (annE dsT a), fst (annE dsT b)]) | UDef _ x a b _ <- us ]
  deps  = [ (x, close [x] (dsLook raw x)) | x <- names ]
  close seen d = case [ g | g <- d, g `elem` names, g `notElem` seen ] of
    []      -> nub (filter (`notElem` names) d)
    (g : _) -> close (g : seen) (d ++ dsLook raw g)
  dsF   = deps ++ ds
  -- the identity of a definition is what it depends on (compared by
  -- conversion); after "%encl" come the parameters of its enclosing
  -- segments, kept only so that a member of an instance can always be
  -- written back as  M[args].x  (Seg.splitDeps)
  encl  = dsLook ds "%params"
  us'   = [ UDef i x (snd (annE dsF a)) (snd (annE dsF b)) (dsLook deps x ++ ["%encl"] ++ encl)
          | UDef i x a b _ <- us ]

annUnits :: DS -> [Unit] -> ([Unit], DS, [Name])
annUnits ds [] = ([], ds, [])
annUnits ds (u : us) = case u of
  ULvl x -> cont [u] (bindVs ds [x]) []
  UPar i x a -> let (d, a') = annE ds a in cont [UPar i x a'] (bindVs ds [x]) d
  UCstr cs -> cont [u] ds (uni [ dl l ++ dl m | Cs l _ m <- cs ])
  UMod i x mus _ ->
    let ownPs = [ y | v <- mus, y <- paramNames v ]
        (mus', _, d) = annUnits (("%params", dsLook ds "%params" ++ ownPs) : ds) mus
        own = [ y | v <- mus, y <- paramNames v ]
        dm  = d \\ own
    in cont [UMod i x mus' dm] ((x, dm) : ds) dm
  UInst i x m -> let (d, m') = annM ds m in cont [UInst i x m'] ((x, d) : ds) d
  ULock _ -> cont [u] ds []
  UDir dr -> cont [UDir (annDir dr)] ds []
  UDef{} -> let (g, rest) = span isGroupUnit (u : us)
                (g', ds', d) = annGroup ds g
                (rest', ds'', d') = annUnits ds' rest
            in (g' ++ rest', ds'', uni [d, d'])
 where
  dl l = uni (map (dsLook ds) (lvNames l))
  cont v ds' d = let (rest, ds'', d') = annUnits ds' us in (v ++ rest, ds'', uni [d, d'])
  paramNames v = case v of
    UPar _ y _ -> [y]
    ULvl y     -> [y]
    _          -> []
  annDir dr = case dr of
    DNormal e -> DNormal (snd (annE ds e))
    DType e   -> DType (snd (annE ds e))
    DConv a b -> DConv (snd (annE ds a)) (snd (annE ds b))
    DFails vs -> let (vs', _, _) = annUnits ds vs in DFails vs'

------------------------------------------------------------------------
-- Entry point: resolve and annotate a whole program (imports expanded)

resolveProgram :: [RUnit] -> Either String [Unit]
resolveProgram rus = do
  let rs0 = RS [] (allLabels rus) "" [] [] M.empty M.empty
  (us, _) <- resUnits rs0 rus 0
  let (us', _, _) = annUnits [] us
  Right us'
