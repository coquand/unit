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

module SegParse (parseUnits, resolveProgram, resolveProgramWith, surveyRecords, RUnit(..)) where

import Seg
import Term (termErrors)
import Data.Char (isAlpha, isDigit, isSpace)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

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
  | RSplit Int [(Name, [Name], [Name], RBody)]   -- c xs | rs -> e  (rs: recursive results)
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
  | RData Int Name [TItem] (Maybe R) [(Name, [TItem], Maybe R)]   -- labels: fields, target
  | RLevel [Name]
  | RCstr [RCs]
  | RModule Bool Name [TItem] [RUnit]       -- True: a record
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
            "opaque", "transparent", "transparent_all", "module", "record", "open", "import",
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

-- The parameters of a module may contain definitions:
--   module M (x : A) (y : B = e) (z : C) { .. }
-- is  module M (x : A) { y : B = e ; z : C ; .. } : from the first
-- definition on, the items are units of the body (a body-less unit is a
-- parameter of the module).
headDefs :: P [RUnit]
headDefs ts
  | isSym "(" ts, Right (u, ts1) <- headDef ts = do
      (rest, ts2) <- headItems ts1
      Right (u : rest, ts2)
  | otherwise = Right ([], ts)
 where
  headItems ts0
    | not (isSym "(" ts0) = Right ([], ts0)
    | Right (u, ts1) <- headDef ts0 = do (rest, ts2) <- headItems ts1
                                         Right (u : rest, ts2)
    | otherwise = do
        ((), ts1) <- sym "(" ts0
        (xs, ts2) <- many1 ident ts1
        ((), ts3) <- sym ":" ts2
        if isKw "Level" ts3
          then do ((), ts4) <- kw "Level" ts3
                  ((), ts5) <- sym ")" ts4
                  (rest, ts6) <- headItems ts5
                  Right (RLevel xs : rest, ts6)
          else do (a, ts4) <- expr ts3
                  ((), ts5) <- sym ")" ts4
                  (rest, ts6) <- headItems ts5
                  Right ([ RDef (occ ts0 - k) y [] a Nothing | (k, y) <- zip [0 ..] xs ] ++ rest, ts6)
  headDef ts0 = do
    ((), ts1) <- sym "(" ts0
    (y, ts2) <- ident ts1
    ((), ts3) <- sym ":" ts2
    (b, ts4) <- expr ts3
    ((), ts5) <- sym "=" ts4
    (e, ts6) <- expr ts5
    ((), ts7) <- sym ")" ts6
    Right (RDef (occ ts0) y [] b (Just (RBody e [])), ts7)

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
  -- anonymous records are not part of the language: a record is declared
  -- (record R { .. }) and its elements are built by new R[..]
  TId "sig" : _    -> Left "sig { .. } is not part of the language: declare a record (record R { .. })"
  TId "struct" : _ -> Left "struct { .. } is not part of the language: build an element with new R[..]"
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

-- c x1 .. xn -> e   or   c x1 .. xn | r1 .. rk -> e  (the recursive results)
branches :: P [(Name, [Name], [Name], RBody)]
branches ts
  | isSym "}" ts = Right ([], ts)
  | otherwise = do
      (c, r1)  <- ident ts
      (xs, r2) <- manyP ident r1
      (rs, r2') <- if isSym "|" r2
                     then do ((), q) <- sym "|" r2
                             many1 ident q
                     else Right ([], r2)
      ((), r3) <- sym "->" r2'
      (e, r4)  <- body r3
      if isSym ";" r4
        then do ((), r5) <- sym ";" r4
                (bs, r6) <- branches r5
                Right ((c, xs, rs, e) : bs, r6)
        else Right ([(c, xs, rs, e)], r4)

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
  | isKw "record" ts = do
      ((), r1) <- kw "record" ts
      (x, r2) <- ident r1
      (tel, r3) <- telescope r2
      ((), r4) <- sym "{" r3
      (us, r5) <- units r4
      ((), r6) <- sym "}" r5
      Right (RModule True x tel us, r6)
  | isKw "module" ts = do
      ((), r1) <- kw "module" ts
      (x, r2) <- ident r1
      if isSym "=" r2
        then do ((), r3) <- sym "=" r2
                (e, r4) <- expr2 r3
                Right (RModInst x e, r4)
        else do (tel, r3) <- telescope r2
                -- a module has no hidden parameters: its arguments are given
                if null [ () | TVarsH _ _ <- tel ]
                  then Right ()
                  else Left ("module " ++ x ++ ": a module has no hidden parameters; write ( .. ) instead of { .. }")
                (pre, r3') <- headDefs r3
                ((), r4) <- sym "{" r3'
                (us, r5) <- units r4
                ((), r6) <- sym "}" r5
                Right (RModule False x tel (pre ++ us), r6)
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

-- a label: its fields and, for an indexed family, its target  : D ps es
labels :: P [(Name, [TItem], Maybe R)]
labels ts
  | isSym ";" ts || isSym "}" ts || null ts = Right ([], ts)
labels ts = do
  (c, r1)   <- ident ts
  (tel, r2) <- telescope r1
  (tg, r2') <- if isSym ":" r2
                 then do ((), r) <- sym ":" r2
                         (a, r') <- expr r
                         Right (Just a, r')
                 else Right (Nothing, r2)
  if isSym "|" r2'
    then do ((), r3) <- sym "|" r2'
            (ls, r4) <- labels r3
            Right ((c, tel, tg) : ls, r4)
    else Right ([(c, tel, tg)], r2')

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
  , miMasks   :: [(Name, [Pos])]
  , miKind    :: SegKind }
  deriving (Show)

data SInfo
  = SVar                       -- lambda/pattern variable, parameter, PN
  | SLvl
  | SDef Id
  | SMod Id ModInfo             -- a segment or an alias: its unique id
  | SVarS ModInfo              -- a variable whose type is a segment
  | SField Name                -- a member of the opened variable c: c.x
  | SOpen MExp String (Maybe ModInfo) -- a member of an opened module (its path)
  deriving (Show)

type Scope = [(Name, SInfo)]

data RS = RS { rsScope :: Scope, rsLabels :: [(Name, Int)], rsPath :: String
             , rsLocks :: [Id], rsMasks :: [(Name, [Pos])]
             -- Map mirrors of rsScope / rsMasks for lookups (the lists keep
             -- the order, which open and the label positions need)
             , rsScopeM :: M.Map Name SInfo, rsMasksM :: M.Map Name [Pos]
             -- the survey (--survey-records): a module used as a type is
             -- not an error, and every segment keeps its head parameters
             , rsSurvey :: Bool
             -- the labels of the indexed families of the program (Nothing:
             -- there is none): a split with one of them, or with no branch,
             -- absorbs a number of indices decided by the filling pass
             , rsIxLabels :: Maybe [Name] }

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
 where f (BVar x a) e = Lam x a e
       f (BLvl x) e   = LLam x e
       f (BCs _) e    = e

lamBB :: [Bind] -> Rhs -> Rhs
lamBB bs b = foldr f b bs
 where f (BVar x a) e = rLam x a e
       f (BLvl x) e   = rLLam x e
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
    Just (SMod i mi)         -> Right (MVar i, mi)      -- by its unique id
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
      missing -> Left (kindWord mi ++ " " ++ miPath mi ++ ": no argument for " ++ unwords missing)
  _ -> Left ("not a module expression: " ++ show r)

-- arguments, positional then named: positional ones fill the parameters in
-- order (Arend: the first unimplemented fields), named ones by name
resArgs :: RS -> ModInfo -> [(Maybe Name, R)] -> Rz [(Name, Arg)]
resArgs rs mi as = do
  let ps = miParams mi
      (pos, named) = span ((== Nothing) . fst) as
  if length pos > length ps then Left (kindWord mi ++ " " ++ miPath mi ++ ": too many arguments") else do
    let posNamed = zip (map fst ps) (map snd pos)
    named' <- mapM (\(n, e) -> case n of
                      Just x  -> Right (x, e)
                      Nothing -> Left "positional argument after a named one") named
    let all' = posNamed ++ named'
    dupCheck (map fst all')
    mapM (\(x, e) -> case lookup x ps of
             Just PTm -> fmap (\e' -> (x, ATm e')) (resE rs e)
             Just PLv -> fmap (\l -> (x, ALv l)) (resLv rs e)
             Nothing  -> Left (kindWord mi ++ " " ++ miPath mi ++ " has no parameter " ++ x)) all'

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
      Just (SDef i) -> Right (Var i)        -- a definition: its unique id
      Just SLvl -> Left ("level variable used as a term: " ++ x)
      Just (SVarS _) -> Right (Var x)
      -- a member of an opened variable: c.x, decided by the filling pass
      Just (SField c) -> Right (ProjU (Var c) x)
      Just (SMod i mi) -> asType mi (SegT (MVar i) [])    -- a record as a type
      Just (SOpen m _ Nothing) -> Right (Acc m x)
      Just (SOpen m _ (Just mi)) -> asType mi (SegT (MSub m x) [])
      Nothing
        | (x, 0) `elem` rsLabels rs -> Right (Con x [])
        | any ((== x) . fst) (rsLabels rs) -> Left ("constructor " ++ x ++ " applied to the wrong number of arguments")
        | otherwise -> Left ("not in scope: " ++ x)
    RU l -> fmap U (resLv rs l)
    RApp a b -> do a' <- resE rs a; b' <- resE rs b; Right (App a' b')
    RLApp a l -> do a' <- resE rs a; l' <- resLv rs l; Right (LApp a' l')
    RLam xs b -> do b' <- resE (bindS rs [ (x, SVar) | x <- xs ]) b
                    Right (foldr (\x -> Lam x Hole) b' xs)
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
                    Right (letsE us' b')
    RTuple es -> do es' <- mapM (resE rs) es
                    Right (foldr1 Pair es')
    RFst a -> fmap Fst (resE rs a)
    RSnd a -> fmap Snd (resE rs a)
    RDot a l
      | isModExp rs a -> do
          (m, mi) <- resM rs a
          if isRecordMI mi then Left ("the member " ++ l ++ " of the record " ++ miPath mi
                                      ++ " is reached through an element, not through the record") else
           if not (null (miParams mi)) then Left ("module " ++ miPath mi ++ " needs arguments") else
            case lookup l (miMembers mi) of
              Just Nothing -> Right (Acc m l)
              Just (Just mi') -> asType mi' (SegT (MSub m l) [])
              Nothing -> Left ("no member " ++ l ++ " in module " ++ miPath mi)
      | Just mi <- recordHead a ->
          Left ("the member " ++ l ++ " of the record " ++ miPath mi
                ++ " is reached through an element, not through the record")
      | otherwise -> do
          a' <- resE rs a
          -- every projection is decided by the filling pass, which knows
          -- the type of a': a field the type fixes is its value, a derived
          -- member is  R[ps].d  at a' (RECORDS.md §3, §4)
          Right (ProjU a' l)
    RInst a as -> do
      (m, mi) <- resHead rs a
      if not (isRecordMI mi || rsSurvey rs) then either Left (const (Left (notRecord mi))) (resM rs r) else do
        fs <- resArgs rs mi as
        Right (SegT m fs)
    RNew a -> do
      (m, mi) <- resM rs a
      if not (isRecordMI mi || rsSurvey rs) then Left ("new " ++ miPath mi ++ ": " ++ notRecord mi) else
       if not (null (miParams mi)) then Left ("new " ++ miPath mi ++ ": arguments missing")
        else Right (New m)            -- the canonical element: a constructor
    RSplit _ _ -> Left splitPlace
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
  asType mi e = if isRecordMI mi || rsSurvey rs then Right e else Left (notRecord mi)
  -- the record named by  R  or  R[..]  (not a variable of record type)
  recordHead a = case a of
    RInst h _ | Right (_, mi) <- resHead rs h, isRecordMI mi -> Just mi
    RVar _ | Right (_, mi) <- resM rs a, isRecordMI mi -> Just mi
    RDot _ _ | Right (_, mi) <- resM rs a, isRecordMI mi -> Just mi
    _ -> Nothing
  spine (RApp a b) as = spine a (b : as)
  spine h as          = (h, as)

splitPlace :: String
splitPlace = "a split must be the body of a definition of a segment (after its lambdas and lets, and in the"
             ++ " branches of a split), not in an expression, a let or a where"

resBody :: RS -> RBody -> Rz Exp
resBody rs (RBody e []) = resE rs e
resBody rs (RBody e us) = do
  (us', rs') <- resLocal rs us
  e' <- resE rs' e
  Right (letsE us' e')

-- the body of a definition of a segment: lambdas, lets and splits, down
-- to expressions (a case tree)
resBodyB :: RS -> RBody -> Rz Rhs
resBodyB rs (RBody e []) = resB rs e
resBodyB rs (RBody e us) = do
  (us', rs') <- resLocal rs us
  b' <- resB rs' e
  Right (letsB us' b')

resB :: RS -> R -> Rz Rhs
resB rs r = case r of
  RLam xs b -> do b' <- resB (bindS rs [ (x, SVar) | x <- xs ]) b
                  Right (foldr (\x -> rLam x Hole) b' xs)
  RLLam xs b -> do b' <- resB (bindS rs [ (x, SLvl) | x <- xs ]) b
                   Right (foldr rLLam b' xs)
  RLet us b -> do (us', rs') <- resLocal rs us
                  b' <- resB rs' b
                  Right (letsB us' b')
  RSplit o bs -> do
    dupCheck [ c | (c, _, _, _) <- bs ]
    bs' <- mapM (\(c, xs, ys, b) -> do
                    dupCheck (filter (/= "_") (xs ++ ys))
                    b' <- resBodyB (bindS rs [ (x, SVar) | x <- xs ++ ys ]) b
                    -- the positions are given by the filling pass, from the data type
                    Right (c, [ (x, Hole) | x <- xs ], [], [ RecR (-1) (-1) [] [] y | y <- ys ], b')) bs
    -- the number of indices: 0 unless a label (or no label) may be of an
    -- indexed family; then the filling pass decides (-1)
    let ls = [ c | (c, _, _, _) <- bs ]
        k = case rsIxLabels rs of
              Just ixl | null ls || any (`elem` ixl) ls -> -1
              _ -> 0
    -- the id is given by pathUnits (the definition and the path)
    let si = rsPath rs ++ "split#" ++ show o
    Right (RhsSplit (DSplit si si Hole [] Hole k bs'))
  _ -> fmap RhsExp (resE rs r)

-- the definitions of a let or where block, as nested lets
letsE :: [Decl] -> Exp -> Exp
letsE us e = foldr (\u acc -> case u of { DDef i x a v -> Let i x a v acc; _ -> acc }) e us

letsB :: [Decl] -> Rhs -> Rhs
letsB us b = foldr (\u acc -> case u of { DDef i x a v -> rLet i x a v acc; _ -> acc }) b us

-- a let / where block: definitions only (no data type: a data type is a
-- declaration of a segment), in sequence
resLocal :: RS -> [RUnit] -> Rz ([Decl], RS)
resLocal rs us = do
  case [ x | RData _ x _ _ _ <- us ] of
    (x : _) -> Left ("the data type " ++ x ++ " is declared in a let or where: a data type must be declared in a"
                     ++ " segment (a module or the file)")
    [] -> Right ()
  let names = [ x | RDef _ x _ _ _ <- us ]
  if length us /= length names then Left "only definitions may appear in a let or where block" else do
    sequentialDefs rs True (\o x -> rsPath rs ++ x ++ "#" ++ show o) us

-- definitions in sequence: each is resolved in the scope of the earlier
-- ones (no recursion by name: recursion is by the eliminators, split with
-- its recursive results); a data type also sees itself, in its fields
-- only (resDef')
sequentialDefs :: RS -> Bool -> (Int -> Name -> Id) -> [RUnit] -> Rz ([Decl], RS)
sequentialDefs rs0 local idOf = go rs0 []
 where
  go r acc [] = Right (reverse acc, r)
  go r acc (v : vs) = do
    let (x, i, m) = case v of
          RDef o y tel _ _ -> (y, idOf o y, telMask tel)
          RData o y _ _ _  -> (y, idOf o y, [])
          _                -> ("", "", [])
        add r' = withMasks (bindS r' [ (x, SDef i) ]) [ (x, m) ]
    -- not in scope in its own definition; a data type sees itself in its
    -- fields (resDef')
    v' <- resDef r local v
    go (add r) (v' : acc) vs

resDef :: RS -> Bool -> RUnit -> Rz Decl
resDef rs local u = either (\m -> Left ("in " ++ rsPath rs ++ unitNm u ++ ": " ++ m)) Right (resDef' rs local u)

unitNm :: RUnit -> String
unitNm u = case u of
  RDef _ x _ _ _ -> x
  RData _ x _ _ _ -> x
  _ -> "?"

resDef' :: RS -> Bool -> RUnit -> Rz Decl
resDef' rs local u = case u of
  RDef o x tel a mb -> do
    (bs, rs1) <- resTel rs tel
    a' <- resE rs1 a
    let i = idOf x o
    case mb of
      Nothing -> Left ("a definition without a body in a let: " ++ x)
      -- a local definition: an expression; a definition of a segment: a
      -- case tree
      Just b | local -> do
        b' <- resBody rs1 { rsPath = i ++ "/" } b
        Right (DDef i x (piB bs a') (lamB bs b'))
      Just b -> do
        b' <- resBodyB rs1 { rsPath = i ++ "/" } b
        Right (defOfRhs i x (piB bs a') (lamBB bs b'))
  RData o x tel ty ls -> do
    dupCheck [ c | (c, _, _) <- ls ]
    (bs, rs1) <- resTel rs tel
    ty' <- case ty of
      Nothing -> Right (U LZero)
      Just t  -> resE rs1 t
    -- the indices (INDEXED.md): the products of the annotation; its
    -- binders name them in the type only
    let ix = [ (if y == "_" then "%ix" ++ show n else y, a) | (n, (y, a)) <- zip [1 :: Int ..] (piTel ty') ]
        k = length ix
        i = idOf x o
    -- the data type sees itself in its fields and targets only (PRIMREC.md 1)
    let rsF = bindS rs1 [ (x, SDef i) ]
    -- the index binders are kept by name around the sum (the core is
    -- named), so an index must not capture a visible name: no index named
    -- like a visible definition, the data type or a parameter (no
    -- shadowing, as for module heads and constructor fields).  A field
    -- may reuse an index name: it is bound inside, and resolver and
    -- evaluation both read it as the field.
    let ixNames = [ y | (y, _) <- piTel ty', y /= "_" ]
    either (\m -> Left ("in the indices of " ++ x ++ ": " ++ m)) Right $ do
      mapM_ (fresh rsF) ixNames
      dupCheck ixNames
    ls' <- mapM (\(c, ctel, mt) -> do
                    freshTel rsF ctel   -- fields are not renamed
                    (cbs, rsC) <- resTel rsF ctel
                    tel' <- mapM (\bd -> case bd of
                                    BVar y a -> Right (y, a)
                                    _ -> Left "only term binders in a constructor") cbs
                    es <- case mt of
                      Nothing | k == 0 -> Right []
                              | otherwise -> Left ("the constructor " ++ c ++ " of the indexed family " ++ x
                                                   ++ " needs its target:  " ++ c ++ " .. : " ++ x ++ " ps es")
                      Just tg | k == 0 -> Left ("the constructor " ++ c ++ " has a target, but " ++ x ++ " has no indices")
                              | otherwise -> do tg' <- resE rsC tg
                                                targetIdx x i bs k c tg'
                    Right (ConDecl c tel' es)) ls
    Right (DData i x (DataDecl (map param bs) ix (piRest ty') ls'))
  _ -> Left "not a definition"
 where
  idOf x o = rsPath rs ++ x ++ (if local then "#" ++ show o else "")
  param b = case b of
    BVar y a -> PTerm y a
    BLvl y   -> PLevel y
    BCs cs   -> PCstr cs

labelsOf :: [RUnit] -> [(Name, Int)]
labelsOf us = concat [ [ (c, sum (map width tel)) | (c, tel, _) <- ls ] | RData _ _ _ _ ls <- us ]
 where width (TVars xs _) = length xs
       width _ = 0

-- the leading products of a resolved type: the indices of an annotation
piTel :: Exp -> [(Name, Exp)]
piTel e = case e of
  Pi y a b -> (y, a) : piTel b
  _ -> []

-- what follows them
piRest :: Exp -> Exp
piRest e = case e of
  Pi _ _ b -> piRest b
  _ -> e

-- the target  D ps es  of a constructor: D applied to exactly its
-- parameters, then to k index expressions (returned)
targetIdx :: Name -> Id -> [Bind] -> Int -> Name -> Exp -> Rz [Exp]
targetIdx x i bs k c tg = case spineOf tg [] of
  (Var h, as)
    | h /= i -> Left bad
    | length as /= length ps + k -> Left ("the target of " ++ c ++ " applies " ++ x ++ " to " ++ show (length as)
                                          ++ " arguments: its " ++ show (length ps) ++ " parameters and "
                                          ++ show k ++ " indices are expected")
    | map toP (take (length ps) as) /= ps ->
        Left ("the target of " ++ c ++ ": " ++ x ++ " is not applied to exactly its parameters (they are uniform)")
    | otherwise -> mapM idx (drop (length ps) as)
  _ -> Left bad
 where
  bad = "the target of " ++ c ++ " must be " ++ x ++ " applied to its parameters and its indices"
  ps = [ p | b <- bs, Just p <- [param b] ]
  param b = case b of
    BVar y _ -> Just (Left y)
    BLvl y   -> Just (Right y)
    BCs _    -> Nothing
  toP a = case a of
    Left (Var y) -> Left y
    Right (LV y) -> Right y
    _ -> Left "?"
  idx a = case a of
    Left e -> Right e
    Right _ -> Left ("the target of " ++ c ++ ": an index is a term, not a level")
  spineOf e acc = case e of
    App a b -> spineOf a (Left b : acc)
    LApp a l -> spineOf a (Right l : acc)
    _ -> (e, acc)

-- the labels of the indexed families of a program (Nothing: none)
ixLabels :: [RUnit] -> Maybe [Name]
ixLabels rus = case go rus of
  [] -> Nothing
  ds -> Just (concat ds)
 where
  go = concatMap one
  one u = case u of
    RData _ _ _ (Just t) ls | indexed t -> [ [ c | (c, _, _) <- ls ] ]
    RDef _ _ _ _ (Just (RBody e ws)) -> go ws ++ inR e
    RModule _ _ _ us -> go us
    RFails us -> go us
    _ -> []
  indexed t = case t of
    RPi _ _ -> True
    RArr _ _ -> True
    _ -> False
  inR e = case e of
    RLet us b -> go us ++ inR b
    RSplit _ bs -> concat [ go ws ++ inR b | (_, _, _, RBody b ws) <- bs ]
    RLam _ b -> inR b
    RApp a b -> inR a ++ inR b
    _ -> []

-- all labels in a program, modules and where blocks included
allLabels :: [RUnit] -> [(Name, Int)]
allLabels = concatMap go
 where
  go u = case u of
    RData{} -> labelsOf [u]
    RDef _ _ _ _ (Just (RBody e ws)) -> allLabels ws ++ inR e
    RModule _ _ _ us -> allLabels us
    RFails us -> allLabels us
    _ -> []
  inR e = case e of
    RLet us b -> allLabels us ++ inR b
    RSplit _ bs -> concat [ allLabels ws ++ inR b | (_, _, _, RBody b ws) <- bs ]
    RLam _ b -> inR b
    RApp a b -> inR a ++ inR b
    _ -> []

-- The units of a module body or of the program, in order.  Consecutive
-- definitions form one mutual group.
resUnits :: RS -> [RUnit] -> Int -> Rz ([Decl], RS)
resUnits rs [] _ = Right ([], rs)
resUnits rs (u : us) n = case u of
  RLevel xs -> do
    mapM_ (fresh rs) xs
    (us', rs') <- resUnits (bindS rs [ (x, SLvl) | x <- xs ]) us n
    Right (map DLvl xs ++ us', rs')
  RCstr cs -> do
    cs' <- mapM (resCs rs) cs
    (us', rs') <- resUnits rs us n
    Right (DCstr cs' : us', rs')
  RDef _ x tel a Nothing -> do
    fresh rs x
    (bs, rs1) <- resTel rs tel
    a' <- resE rs1 a
    (us', rs') <- resUnits (withMasks (bindS rs [(x, if null tel then varInfo rs a else SVar)])
                                      [(x, telMask tel)]) us n
    Right (DVar (rsPath rs ++ x) x (piB bs a') : us', rs')
  RModule isRec x tel body -> do
    fresh rs x
    -- a record's body: fields and definitions only
    case [ () | isRec, b <- body, notInRecord b ] of
      [] -> Right ()
      _  -> Left ("the record " ++ x ++ " may contain only fields, definitions and opens (no module, record, level or constraint)")
    let rsIn = rs { rsPath = rsPath rs ++ x ++ "." }
    -- head parameters are not renamed: no shadowing, as in the body
    either (\m -> Left ("in the head of " ++ x ++ ": " ++ m)) Right (freshTel rs tel)
    (bs, rsTel) <- resTel rsIn tel
    let varOf y = maybe SVar id (M.lookup y (rsScopeM rsTel))
    let headUnits = map bindUnit bs
        bindUnit bd = case bd of
          BVar y a -> DVar (rsPath rsIn ++ y) y a
          BLvl y   -> DLvl y
          BCs cs   -> DCstr cs
        rsHead = bindS rsIn (concatMap bindScope bs)
        bindScope bd = case bd of
          BVar y _ -> [(y, varOf y)]
          BLvl y   -> [(y, SLvl)]
          BCs _    -> []
    (bodyUnits, rsBody) <- resUnits rsHead body 0
    -- a record body has no data type and no split
    case [ unitName v | isRec, v <- bodyUnits, dataOrSplit v ] of
      [] -> Right ()
      (y : _) -> Left ("the record " ++ x ++ " contains a data type or a split (" ++ y
                       ++ "): a record has no data type, no split and no record (as no module, level or constraint)")
    let all' = headUnits ++ bodyUnits
        mi = ModInfo [ (unitName v, k) | v <- all', Just k <- [paramKind v] ]
                     (membersOf rsBody rsHead ++ [ (unitName v, Nothing) | v@(DVar{}) <- headUnits ])
                     (rsPath rs ++ x)
                     [ (y, ps) | (y, _) <- membersOf rsBody rsHead
                               , Just ps <- [M.lookup y (rsMasksM rsBody)], PH `elem` ps ]
                     kind
        heads = SRecord [ unitName v | v <- headUnits, Just _ <- [paramKind v] ]
        kind = if isRec then heads else SModule
        ukind = if rsSurvey rs then heads else kind
    -- the lock strategy is global and positional: what the body set persists
    let rsAfter = (bindS rs [(x, SMod (rsPath rs ++ x) mi)]) { rsLocks = rsLocks rsBody }
        us2 = case recordCon x tel body of
          Just c@(RDef _ mk _ _ _)
            | isRec
            , mk `notElem` concatMap definedNames us
            , Right _ <- resUnits rsAfter [c] n -> c : us
          _ -> us
    (us', rs') <- resUnits rsAfter us2 n
    Right (mkSeg (rsPath rs ++ x) x ukind all' : us', rs')
  RModInst x e -> do
    fresh rs x
    case e of
      RInst h _ | Right (_, mi) <- resHead rs h, isRecordMI mi ->
        Left ("module " ++ x ++ " = " ++ miPath mi ++ "[..]: a record is not a module")
      _ -> Right ()
    (m, mi) <- resM rs e
    -- a record can be renamed, not instantiated as a module
    let recArgs = case m of { MApp _ _ -> isRecordMI mi; _ -> False }
    if recArgs then Left ("module " ++ x ++ " = " ++ miPath mi ++ "[..]: a record is not a module") else
     if not (null (miParams mi)) && not (isRecordMI mi) then Left ("module " ++ miPath mi ++ " needs arguments") else do
      (us', rs') <- resUnits (bindS rs [(x, SMod (rsPath rs ++ x) mi)]) us n
      Right (DInst (rsPath rs ++ x) x m : us', rs')
  ROpen _ (RVar c) | Just (SVarS mi) <- look rs c -> do
    let opened = [ (y, SField c) | (y, Nothing) <- miMembers mi, not (M.member y (rsScopeM rs)) ]
    resUnits (withMasks (bindS rs opened) (miMasks mi)) us n
  ROpen o e -> do
    case e of
      RInst h _ | Right (_, mi) <- resHead rs h, isRecordMI mi ->
        Left ("open " ++ miPath mi ++ "[..]: a record is not a module (open an element)")
      _ -> Right ()
    (m, mi) <- resM rs e
    if isRecordMI mi then Left ("open " ++ miPath mi ++ ": a record is not a module (open an element)") else
     if not (null (miParams mi)) then Left ("module " ++ miPath mi ++ " needs arguments") else do
      let (pre, m') = case m of
            -- unique in the whole program: o (the tokens left) is unique only
            -- within one file, and a nested open with the same name would
            -- shadow an enclosing one
            MApp _ _ -> let nm = "open#" ++ show o ++ "@" ++ map (\c -> if c == '.' then '/' else c) (rsPath rs)
                        in ([DInst (rsPath rs ++ nm) nm m], MVar (rsPath rs ++ nm))
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
    Right (DLock [] : us', rs')
  RNormal e -> directive (fmap DNormal (resE rs e))
  RType e -> directive (fmap DType (resE rs e))
  RConv a b -> directive (do a' <- resE rs a; b' <- resE rs b; Right (DConv a' b'))
  RFails xs -> case resUnits rs xs n of
    Left msg -> directive (Right (DFails [DDir (DNormal (Var ("#resolution failed: " ++ msg)))]))
    Right (xs', _) -> directive (Right (DFails xs'))
  _ -> do
    -- consecutive definitions (and data): SEQUENTIAL scope, each sees only
    -- the earlier ones; a data type also sees itself (in its fields)
    let isDefU v = case v of
          RDef _ _ _ _ (Just _) -> True
          RData{} -> True
          _ -> False
        (g, rest) = span isDefU (u : us)
        names = [ x | RDef _ x _ _ _ <- g ] ++ [ x | RData _ x _ _ _ <- g ]
    mapM_ (fresh rs) names
    dupCheck names
    (g', rsG) <- sequentialDefs rs False (\_ x -> rsPath rs ++ x) g
    (us', rs') <- resUnits rsG rest n
    Right (g' ++ us', rs')
 where
  directive me = do
    d <- me
    (us', rs') <- resUnits rs us n
    Right (DDir d : us', rs')
  lockCmd e f = do
    i <- lockId rs e
    let s = f i (rsLocks rs)
    (us', rs') <- resUnits rs { rsLocks = s } us n
    Right (DLock s : us', rs')

-- a data type, or a definition whose body is a split
dataOrSplit :: Decl -> Bool
dataOrSplit u = case u of
  DData{} -> True
  DDef{} -> False
  DSplit{} -> True
  _ -> False

isRecordMI :: ModInfo -> Bool
isRecordMI mi = case miKind mi of
  SRecord _ -> True
  SModule   -> False

kindWord :: ModInfo -> String
kindWord mi = if isRecordMI mi then "record" else "module"

notRecord :: ModInfo -> String
notRecord mi = miPath mi ++ " is a module; declare it with `record` to use it as a type"

-- the units a record body may not contain (an open of a module instance
-- is allowed: it only brings the module's members into scope, with their
-- identities)
notInRecord :: RUnit -> Bool
notInRecord u = case u of
  RModule{}  -> True
  RModInst{} -> True
  RLevel _   -> True
  RCstr _    -> True
  RImport _  -> True
  _          -> False

-- The constructor of a record.  A record gets
--   mkM (params) (fields) : M[params] = new M[params, fields] ,
-- notation for new: the checker evaluates an access to it to its body
-- (Seg.isNewDef), so it is never opened.
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
  RModule _ y _ _ -> [y]
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

paramKind :: Decl -> Maybe PKind
paramKind u = case u of
  DVar{} -> Just PTm
  DLvl _ -> Just PLv
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
    SMod _ mi -> Just (Just mi)
    _        -> Nothing

fresh :: RS -> Name -> Rz ()
fresh rs x = case look rs x of
  Just (SOpen _ _ _) -> Right ()
  Just (SField _) -> Right ()
  Just _  -> Left ("the name " ++ x ++ " is already declared (no shadowing)")
  Nothing -> Right ()

-- the names a telescope binds that are kept (not renamed by binderE):
-- module and record heads, constructor fields
freshTel :: RS -> [TItem] -> Rz ()
freshTel rs tel = do
  let xs = concat [ case t of { TVars ys _ -> ys; TVarsH ys _ -> ys; TLvls ys -> ys; TCs _ -> [] } | t <- tel ]
  mapM_ (fresh rs) (filter (/= "_") xs)
  dupCheck (filter (/= "_") xs)

dupCheck :: [Name] -> Rz ()
dupCheck [] = Right ()
dupCheck (x : xs)
  | x `elem` xs = Left ("the name " ++ x ++ " is declared twice")
  | otherwise   = dupCheck xs

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Entry point: resolve and annotate a whole program (imports expanded)

resolveProgram :: [RUnit] -> Either String [Decl]
resolveProgram = resolveProgramWith True

-- with  term : the restrictions, positivity and termination (Term) are
-- enforced: errors of the program, and inside #fails a failure of the block
resolveProgramWith :: Bool -> [RUnit] -> Either String [Decl]
resolveProgramWith term rus = do
  let rs0 = RS [] (allLabels rus) "" [] [] M.empty M.empty False (ixLabels rus)
  (us, _) <- resUnits rs0 rus 0
  let us' = pathUnits (binderUnits us)    -- paths after renaming: the names a path
                                          -- reads are those its environment binds
  case shadowReport us' of
    [] -> Right ()
    bad -> Left (unlines ("a variable or level may not have the name of a variable or level in scope (no shadowing):" : map ("  " ++) (take 400 bad)))
  if not term then Right us' else do
    case termErrors us' us' of
      [] -> Right ()
      bad -> Left (unlines ("positivity and termination:" : map ("  " ++) (take 20 bad)))
    Right (map (failsTerm us') us')

-- a #fails block rejected by Term fails (as one that does not resolve)
failsTerm :: [Decl] -> Decl -> Decl
failsTerm whole u = case u of
  DDir (DFails vs) -> case [ "#termination: " ++ m | m <- termErrors whole vs ] of
    [] -> DDir (DFails (map (failsTerm whole) vs))
    (m : _) -> DDir (DFails [DDir (DNormal (Var m))])
  _ | Just _ <- segParts u -> mapSeg (map (failsTerm whole)) u
  _ -> u

mapL :: (Int -> a -> (Int, b)) -> Int -> [a] -> (Int, [b])
mapL _ n []       = (n, [])
mapL f n (x : xs) = let (n1, y) = f n x
                        (n2, ys) = mapL f n1 xs
                    in (n2, y : ys)

------------------------------------------------------------------------
-- Splits and sums are named by their definition (mTT10 section 5: f_B,
-- d_L).  A split or a sum stands at a DEFINITION POSITION: the body of a
-- definition f, after lambdas and branches of splits.  Its closure B rho is
-- then  f  applied to the values in rho of the path that leads to it (the
-- lambda variables, the constructors of the branches with their pattern
-- variables), which is how it is read back.  The path is kept in the id.

pathUnits :: [Decl] -> [Decl]
pathUnits = map unit
 where
  unit u = case u of
    d@(DSplit i _ _ _ _ _ _) -> pathSplit i [] d
    _ | Just _ <- segParts u -> mapSeg pathUnits u
    DDir (DFails vs) -> DDir (DFails (pathUnits vs))
    _               -> u

-- a split declaration of the definition i at the path p: its case is
-- named by the path through its context; a nested split is named by its
-- occurrence
pathSplit :: Id -> [[String]] -> Decl -> Decl
pathSplit i p d = case d of
  DSplit di x a delta ty k bs ->
    let p' = p ++ concat [ case c of { DVar _ y _ -> [["v", y]]; DLvl y -> [["l", y]]; _ -> [] } | c <- delta ]
    in DSplit di x a delta ty k [ (c, xs, is, rs, pathRhs i (p' ++ [("c" : c : map fst xs)]) b') | (c, xs, is, rs, b') <- bs ]
  _ -> d

pathRhs :: Id -> [[String]] -> Rhs -> Rhs
pathRhs i p r = case r of
  RhsExp _ -> r
  RhsSplit d -> case pathSplit i p d of
    -- a nested split is named by the path that leads to it
    DSplit _ _ a delta ty k bs -> RhsSplit (DSplit (pathId i p) (pathId i p) a delta ty k bs)
    d' -> RhsSplit d'


------------------------------------------------------------------------
-- No shadowing between variables and levels (Wang).  The dependencies of
-- a definition and the values of its variables are found by name, so a
-- binder must not hide a variable or level of the same name.  Segments,
-- opened members and definitions may be hidden: they are reached through
-- M.x or by their ids.

shadowReport :: [Decl] -> [String]
shadowReport = units "" S.empty
 where
  units _ _ [] = []
  units w sc (u : us) = case u of
    DVar i x a      -> new i sc x ++ expr i sc a ++ units w (S.insert x sc) us
    DLvl x          -> new w sc x ++ units w (S.insert ('%' : x) (S.insert x sc)) us
    DDef i _ a b  -> expr i sc a ++ expr i sc b ++ units w sc us
    d@(DSplit i _ a _ _ _ _) -> expr i sc a ++ split i sc d ++ units w sc us
    DData i _ dd  -> expr i sc (dataType dd) ++ dataB i sc (dataBinders dd) (ddCons dd) ++ units w sc us
    _ | Just (i, _, _, vs) <- segParts u -> units i sc vs ++ units w sc us
    DInst i _ m     -> mexp i sc m ++ units w sc us
    DDir (DFails _) -> units w sc us
    DDir d          -> concat [ expr w sc e | e <- dirExps d ] ++ units w sc us
    _               -> units w sc us
  dirExps d = case d of { DNormal e -> [e]; DType e -> [e]; DConv a b -> [a, b]; _ -> [] }
  new w sc x = [ w ++ ": " ++ x ++ (if S.member ('%' : x) sc then " (a level)" else " (a variable)") | x /= "_", S.member x sc ]
  binds w sc xs k = concat [ new w sc x | x <- xs ] ++ k (foldr S.insert sc xs)
  expr w sc e = case e of
    Lam x d b    -> expr w sc d ++ binds w sc [x] (\sc' -> expr w sc' b)
    Pi x a b     -> expr w sc a ++ binds w sc [x] (\sc' -> expr w sc' b)
    Sig x a b    -> expr w sc a ++ binds w sc [x] (\sc' -> expr w sc' b)
    LPi x a      -> binds w sc [x] (\sc' -> expr w (S.insert ('%' : x) sc') a)
    LLam x a     -> binds w sc [x] (\sc' -> expr w (S.insert ('%' : x) sc') a)
    Let _ _ a v b -> expr w sc a ++ expr w sc v ++ expr w sc b
    Acc m _      -> mexp w sc m
    SegT m fs    -> mexp w sc m ++ concat [ expr w sc a | (_, ATm a) <- fs ]
    New m        -> mexp w sc m
    _            -> concatMap (expr w sc) (subs e)
  body w sc b = case b of
    RhsExp e        -> expr w sc e
    RhsSplit d      -> split w sc d
  split w sc d = case d of
    DSplit _ _ _ delta ty _ bs -> ctx w sc delta ty bs
    _ -> []
  ctx w sc delta ty bs = case delta of
    DVar _ x a : ds -> expr w sc a ++ binds w sc [x] (\sc' -> ctx w sc' ds ty bs)
    DLvl x : ds     -> binds w sc [x] (\sc' -> ctx w (S.insert ('%' : x) sc') ds ty bs)
    DDef _ _ a v : ds -> expr w sc a ++ expr w sc v ++ ctx w sc ds ty bs
    _ : ds          -> ctx w sc ds ty bs
    [] -> expr w sc ty ++ concat [ binds w sc (map fst xs ++ recNames rs) (\sc' -> concatMap (expr w sc' . snd) xs ++ concatMap (expr w sc') is ++ body w sc' b') | (_, xs, is, rs, b') <- bs ]
  -- a data type: its parameters and indices (as lambdas), then its labels
  dataB w sc ps cs = case ps of
    PTerm x _ : ps' -> binds w sc [x] (\sc' -> dataB w sc' ps' cs)
    PLevel x : ps'  -> binds w sc [x] (\sc' -> dataB w (S.insert ('%' : x) sc') ps' cs)
    PCstr _ : ps'   -> dataB w sc ps' cs
    [] -> concat [ tel w sc t ++ concat [ expr w (foldr S.insert sc (map fst t)) e | e <- es ] | ConDecl _ t es <- cs ]
  tel _ _ [] = []
  tel w sc ((x, a) : t) = new w sc x ++ expr w sc a ++ tel w (S.insert x sc) t
  mexp w sc m = case m of
    MVar _    -> []
    MSub a _  -> mexp w sc a
    MApp a as -> mexp w sc a ++ concat [ expr w sc e | ATm e <- as ]
  subs e = case e of
    App a b -> [a, b]; Pair a b -> [a, b]; Fst a -> [a]; Snd a -> [a]; Con _ as -> as
    Proj a _ -> [a]; ProjU a _ -> [a]
    Id a x y -> [a, x, y]; Refl a -> [a]; IdJ a x c d y p -> [a, x, c, d, y, p]
    LApp a _ -> [a]; CPi _ a -> [a]
    _ -> []

------------------------------------------------------------------------
-- Code identities.  Every binder local to an expression (lambda, Pi,
-- Sigma, level lambda and Pi, pattern variables) gets a unique internal
-- name  x\1id , and its occurrences with it.  Two closures with the same
-- binder name are then the same occurrence of code (Seg.eqClos): the same
-- body, in an environment of the same shape.  Segment parameters, levels,
-- record fields and constructor telescopes keep their names.  The id is
-- never printed.

binderUnits :: [Decl] -> [Decl]
binderUnits = map unit
 where
  unit u = case u of
    DDef i x a b   -> DDef i x (binderE (i ++ ":") a) (binderE (i ++ "=") b)
    d@(DSplit i _ _ _ _ _ _) -> case snd (binderS (i ++ "=") M.empty 0 d) of
      DSplit _ x a delta ty k bs -> DSplit i x (binderE (i ++ ":") a) delta ty k bs
      d' -> d'
    DData i x dd   -> DData i x (binderData (i ++ "=") dd)
    DVar i x a     -> DVar i x (binderE (i ++ ":") a)
    _ | Just _ <- segParts u -> mapSeg binderUnits u
    DInst i x m    -> DInst i x (binderM (i ++ "=") m)
    DDir d         -> DDir (case d of
                        DNormal e -> DNormal (binderE "dir" e)
                        DType e   -> DType (binderE "dir" e)
                        DConv a b -> DConv (binderE "dir1" a) (binderE "dir2" b)
                        DFails vs -> DFails (binderUnits vs))
    _              -> u

binderE :: String -> Exp -> Exp
binderE pre e0 = snd (binderGo pre M.empty 0 e0)

binderBind :: String -> M.Map Name Name -> Int -> Name -> (Name, M.Map Name Name, Int)
binderBind pre ren n x
  | x == "_"  = (x, M.delete x ren, n)
  | otherwise = let x' = x ++ "\1" ++ pre ++ show n in (x', M.insert x x' ren, n + 1)

-- a right-hand side: its lambdas, lets and pattern variables as in an
-- expression
binderB :: String -> M.Map Name Name -> Int -> Rhs -> (Int, Rhs)
binderB pre ren n b = case b of
  RhsExp e -> let (n1, e') = binderGo pre ren n e in (n1, RhsExp e')
  RhsSplit d -> let (n1, d') = binderS pre ren n d in (n1, RhsSplit d')

-- a split declaration: its context, then its case
binderS :: String -> M.Map Name Name -> Int -> Decl -> (Int, Decl)
binderS pre ren0 n0 d = case d of
  DSplit i x a delta0 ty0 sk bs -> ctx ren0 n0 delta0 []
   where
    ctx ren n delta acc = case delta of
      DVar j y b : ds -> let (n1, b') = binderGo pre ren n b; (y', ren', n2) = binderBind pre ren n1 y
                         in ctx ren' n2 ds (acc ++ [DVar j y' b'])
      DLvl y : ds -> let (y', ren', n1) = binderBind pre ren n y in ctx ren' n1 ds (acc ++ [DLvl y'])
      DDef j y b v : ds -> let (n1, b') = binderGo pre ren n b; (n2, v') = binderGo pre ren n1 v
                           in ctx ren n2 ds (acc ++ [DDef j y b' v'])
      c : ds -> ctx ren n ds (acc ++ [c])
      [] -> let (nn, ty, bs') = cas ren n in (nn, DSplit i x a acc ty sk bs')
    cas ren n = let (n0', ty) = binderGo pre ren n ty0; (n1, bs') = mapL (\k (c, xs, is, rs, b') ->
                                      let (xs', ren', k1) = foldl (\(acc, r, kk) (x, a) -> let (kk0, a') = binderGo pre r kk a; (x', r', kk') = binderBind pre r kk0 x in (acc ++ [(x', a')], r', kk')) ([], ren, k) xs
                                          (k1i, is') = mapL (binderGo pre ren') k1 is
                                          (ys', ren'', k1') = foldl (\(acc, r, kk) x -> let (x', r', kk') = binderBind pre r kk x in (acc ++ [x'], r', kk')) ([], ren', k1i) (recNames rs)
                                          (k2, b'') = binderB pre ren'' k1' b'
                                      in (k2, (c, xs', is', [ RecR j m ds es y | (RecR j m ds es _, y) <- zip rs ys' ], b''))) n0' bs
                in (n1, ty, bs')
  _ -> (n0, d)

-- a data declaration: its parameters and indices are bound in order
-- (as by its type and its lambdas, one renaming); a target is in the scope
-- of the fields (kept)
binderData :: String -> DataDecl -> DataDecl
binderData pre dd = DataDecl ps' ix' srt' cs'
 where
  stepP (acc, ren, n) p = case p of
    PTerm x a -> let (n1, a') = binderGo pre ren n a; (x', ren', n2) = binderBind pre ren n1 x in (acc ++ [PTerm x' a'], ren', n2)
    PLevel x  -> let (x', ren', n1) = binderBind pre ren n x in (acc ++ [PLevel x'], ren', n1)
    PCstr cs  -> (acc ++ [PCstr [ Cs (binderLv ren l) r (binderLv ren m) | Cs l r m <- cs ]], ren, n)
  (ps', ren1, n1) = foldl stepP ([], M.empty, 0) (ddParams dd)
  stepI (acc, ren, n) (y, a) = let (n1, a') = binderGo pre ren n a; (y', ren', n2) = binderBind pre ren n1 y in (acc ++ [(y', a')], ren', n2)
  (ix', ren2, n2) = foldl stepI ([], ren1, n1) (ddIndices dd)
  (n3, srt') = binderGo pre ren2 n2 (ddSort dd)
  (_, cs') = mapL (\k (ConDecl c tel es) ->
                    let (k', tel') = binderTel pre ren2 k tel
                        ren' = foldr M.delete ren2 (map fst tel)
                        (k'', es') = mapL (binderGo pre ren') k' es
                    in (k'', ConDecl c tel' es')) n3 (ddCons dd)

binderLv :: M.Map Name Name -> Lv -> Lv
binderLv ren l = case l of
  LV x     -> LV (M.findWithDefault x x ren)
  LSuc m   -> LSuc (binderLv ren m)
  LMax a b -> LMax (binderLv ren a) (binderLv ren b)
  LZero    -> LZero

-- a constructor telescope: its names are kept (they are its fields)
binderTel :: String -> M.Map Name Name -> Int -> Tel -> (Int, Tel)
binderTel _ _ k [] = (k, [])
binderTel pre ren k ((x, a) : t) = let (k1, a') = binderGo pre ren k a; (k2, t') = binderTel pre (M.delete x ren) k1 t in (k2, (x, a') : t')

binderGo :: String -> M.Map Name Name -> Int -> Exp -> (Int, Exp)
binderGo pre = go
 where
  bind = binderBind pre
  go :: M.Map Name Name -> Int -> Exp -> (Int, Exp)
  go ren n e = case e of
    Var x        -> (n, Var (M.findWithDefault x x ren))
    U l          -> (n, U (lv ren l))
    App a b      -> two App a b
    Lam x d b    -> let (n1, d') = go ren n d; (x', ren', n2) = bind ren n1 x; (n3, b') = go ren' n2 b in (n3, Lam x' d' b')
    Pi x a b     -> let (n1, a') = go ren n a; (x', ren', n2) = bind ren n1 x; (n3, b') = go ren' n2 b in (n3, Pi x' a' b')
    Sig x a b    -> let (n1, a') = go ren n a; (x', ren', n2) = bind ren n1 x; (n3, b') = go ren' n2 b in (n3, Sig x' a' b')
    LPi x a      -> let (x', ren', n1) = bind ren n x; (n2, a') = go ren' n1 a in (n2, LPi x' a')
    LLam x a     -> let (x', ren', n1) = bind ren n x; (n2, a') = go ren' n1 a in (n2, LLam x' a')
    LApp a l     -> let (n1, a') = go ren n a in (n1, LApp a' (lv ren l))
    CPi cs a     -> let (n1, a') = go ren n a in (n1, CPi [ Cs (lv ren l) r (lv ren m) | Cs l r m <- cs ] a')
    Let i x a t b -> let (n1, a') = go ren n a; (n2, t') = go ren n1 t; (n3, b') = go ren n2 b in (n3, Let i x a' t' b')
    Con c as     -> let (n1, as') = mapL (go ren) n as in (n1, Con c as')
    Pair a b     -> two Pair a b
    Fst a        -> one Fst a
    Snd a        -> one Snd a
    Proj a l     -> one (\a' -> Proj a' l) a
    ProjU a l    -> one (\a' -> ProjU a' l) a
    Mem m as l a -> one (\a' -> Mem m as l a') a      -- never in source
    Id a x y     -> let (n1, [a', x', y']) = mapL (go ren) n [a, x, y] in (n1, Id a' x' y')
    Refl a       -> one Refl a
    IdJ a x c d y p -> let (n1, [a', x', c', d', y', p']) = mapL (go ren) n [a, x, c, d, y, p] in (n1, IdJ a' x' c' d' y' p')
    Acc m x      -> let (n1, m') = goM ren n m in (n1, Acc m' x)
    SegT m fs    -> let (n1, m') = goM ren n m
                        (n2, fs') = mapL (\k (x, a) -> let (k', a') = goA ren k a in (k', (x, a'))) n1 fs
                    in (n2, SegT m' fs')
    New m        -> let (n1, m') = goM ren n m in (n1, New m')
    Hole         -> (n, Hole)
   where
    one f a = let (n1, a') = go ren n a in (n1, f a')
    two f a b = let (n1, a') = go ren n a; (n2, b') = go ren n1 b in (n2, f a' b')
  goM ren n m = case m of
    MVar _    -> (n, m)
    MSub a x  -> let (n1, a') = goM ren n a in (n1, MSub a' x)
    MApp a as -> let (n1, a') = goM ren n a; (n2, as') = mapL (goA ren) n1 as in (n2, MApp a' as')
  goA ren n a = case a of
    ATm e -> let (n1, e') = go ren n e in (n1, ATm e')
    ALv l -> (n, ALv (lv ren l))
  lv ren l = case l of
    LV x     -> LV (M.findWithDefault x x ren)
    LSuc m   -> LSuc (lv ren m)
    LMax a b -> LMax (lv ren a) (lv ren b)
    LZero    -> LZero

binderM :: String -> MExp -> MExp
binderM pre m = case m of
  MVar _    -> m
  MSub a x  -> MSub (binderM pre a) x
  MApp a as -> MApp (binderM pre a) [ case a' of { ATm e -> ATm (binderE (pre ++ show k ++ ".") e); ALv _ -> a' } | (k, a') <- zip [0 :: Int ..] as ]

------------------------------------------------------------------------
-- The survey of the segments used as records (--survey-records): the
-- program is resolved with modules allowed as types, then every segment
-- used as a type or with  new  is listed with its head parameters, its
-- body fields, its derived members, its uses as a module, and the body
-- units a record may not contain.

surveyRecords :: [RUnit] -> Either String String
surveyRecords rus = do
  let rs0 = RS [] (allLabels rus) "" [] [] M.empty M.empty True (ixLabels rus)
  (us, _) <- resUnits rs0 rus 0
  let segs  = M.fromList [ (i, (k, vs)) | (i, k, vs) <- allSegs us ]
      insts = M.fromList [ (i, m) | (i, m) <- allInsts us ]
      segOf m = case m of
        MVar i -> chase i
        MApp n _ -> segOf n
        MSub n x -> segOf n >>= \t -> chase (t ++ "." ++ x)
      chase i | M.member i segs = Just i
              | Just m <- M.lookup i insts = segOf m
              | otherwise = Nothing
      uses = [ (t, k) | (k, m) <- concatMap unitUses us, Just t <- [segOf m] ]
      count t k = length [ () | (t', k') <- uses, t' == t, k' == k ]
      asRecord = S.toList (S.fromList [ t | (t, k) <- uses, k /= "module" ])
      line t = case M.lookup t segs of
        Nothing -> t ++ "  (not found)"
        Just (SRecord hs, vs) ->
          let body = dropHeads hs vs
              fields = [ x | DVar _ x _ <- body ]
              derived = [ x | DDef _ x _ _ <- body ]
              bad = [ what | v <- body, Just what <- [badUnit v] ]
          in t ++ "\n    head:    " ++ unwords hs
               ++ "\n    fields:  " ++ unwords fields
               ++ "\n    derived: " ++ show (length derived)
               ++ "\n    uses:    type " ++ show (count t "type") ++ ", new " ++ show (count t "new")
               ++ ", module " ++ show (count t "module")
               ++ (if null bad then "" else "\n    NOT ALLOWED IN A RECORD: " ++ unwords (S.toList (S.fromList bad)))
        Just _ -> t
  Right (unlines (map line asRecord) ++ show (length asRecord) ++ " segments used as records")
 where
  allSegs = concatMap seg
  seg u = case u of
    _ | Just (i, _, k, vs) <- segParts u -> (i, k, vs) : allSegs vs
    _ -> []
  allInsts = concatMap inst
  inst u = case u of
    DInst i _ m -> [(i, m)]
    _ | Just (_, _, _, vs) <- segParts u -> allInsts vs
    _ -> []
  -- the units after the head parameters (and their constraints)
  dropHeads hs vs = case vs of
    DVar _ x _ : rest | x `elem` hs -> dropHeads hs rest
    DLvl x : rest | x `elem` hs -> dropHeads hs rest
    DCstr _ : rest -> dropHeads hs rest
    _ -> vs
  badUnit v = case v of
    _ | Just (_, x, _, _) <- segParts v -> Just ("module/" ++ x)
    DInst _ x _  -> if "open#" `isPrefixOfS` x then Nothing else Just ("instance/" ++ x)
    DLvl _       -> Just "level"
    DCstr _      -> Just "constraint"
    _            -> Nothing
  isPrefixOfS a b = take (length a) b == a
  unitUses u = case u of
    DDef _ _ a b -> expUses a ++ expUses b
    d@DSplit{} -> splitUses d
    DData _ _ dd -> expUses (dataType dd) ++ concat [ expUses t | ConDecl _ tel es <- ddCons dd, t <- map snd tel ++ es ]
    DVar _ _ a -> expUses a
    _ | Just (_, _, _, vs) <- segParts u -> concatMap unitUses vs
    DInst _ _ m -> modUses m
    DDir d -> case d of
      DNormal e -> expUses e
      DType e -> expUses e
      DConv a b -> expUses a ++ expUses b
      DFails vs -> concatMap unitUses vs
    _ -> []
  -- a module expression used as a module: its head, and the segments it
  -- goes through
  modUses m = ("module", m) : inner m
  inner m = case m of
    MVar _ -> []
    MSub n _ -> modUses n
    MApp n as -> inner n ++ concat [ expUses e | ATm e <- as ]
  -- in a type or new, only the segments it goes through are used as modules
  through m = case m of
    MVar _ -> []
    MSub n _ -> modUses n
    MApp n as -> through n ++ concat [ expUses e | ATm e <- as ]
  expUses e = case e of
    SegT m fs -> ("type", m) : through m ++ concat [ expUses a | (_, ATm a) <- fs ]
    New m -> ("new", m) : through m
    Acc m _ -> modUses m
    Let _ _ a v b -> expUses a ++ expUses v ++ expUses b
    Lam _ d b -> expUses d ++ expUses b
    Pi _ a b -> expUses a ++ expUses b
    Sig _ a b -> expUses a ++ expUses b
    LPi _ a -> expUses a
    LLam _ a -> expUses a
    _ -> concatMap expUses (subE e)
  bodyUses b = case b of
    RhsExp e -> expUses e
    RhsSplit d -> splitUses d
  splitUses d = case d of
    DSplit _ _ a delta ty _ bs -> expUses a ++ concat [ case c of { DVar _ _ t -> expUses t; DDef _ _ t v -> expUses t ++ expUses v; _ -> [] } | c <- delta ]
                                    ++ expUses ty ++ concat [ concatMap (expUses . snd) xs ++ concatMap expUses is ++ bodyUses b' | (_, xs, is, _, b') <- bs ]
    _ -> []
  subE e = case e of
    App a b -> [a, b]; Pair a b -> [a, b]; Fst a -> [a]; Snd a -> [a]; Con _ as -> as
    Proj a _ -> [a]; ProjU a _ -> [a]
    Id a x y -> [a, x, y]; Refl a -> [a]; IdJ a x c d y p -> [a, x, c, d, y, p]
    LApp a _ -> [a]; CPi _ a -> [a]
    _ -> []
