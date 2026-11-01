-- Loader.hs -- Ralph Loader's loader.c (Bignum Bakeoff, 2001) read as a
-- proof machine for the Calculus of Constructions.
--
-- Source: http://djm.cc/bignum-results.txt, entry {loader.c}.
--
-- Three parts.
--   1. Literal: the C program on the free pairing algebra.  Every
--      positive integer is uniquely P(y,x) = (2y+1)*2^x; loader.c only
--      ever looks at numbers through P, L (= y), Z (= x) and a few
--      small-number tests, so a number is kept as a tree.  The global r
--      is local in effect, and the global a is only written (a stack of
--      judgements), so both become pure.
--   2. Structured: the same machine on terms of CC with de Bruijn
--      indices.  The judgements are produced only by rules, as in an LCF
--      kernel; all terms stay beta-normal (substitution is hereditary),
--      so conversion is equality of codes.
--   3. Test: (1) and (2) produce the same stack of judgements, and every
--      judgement is accepted by an independent, textbook checker for CC.
module Main where

import qualified Data.Map as M
import System.Environment (getArgs)

------------------------------------------------------------------------
-- 1. Literal

data N = O | P N N deriving (Eq, Ord, Show)

fromI :: Integer -> N
fromI 0 = O
fromI n = let z = tz n in P (fromI ((n `div` 2 ^ z - 1) `div` 2)) (fromI z)
  where tz k = if odd k then 0 else 1 + tz (k `div` 2)

toI :: N -> Integer
toI O = 0
toI (P y x) = (2 * toI y + 1) * 2 ^ toI x

lL, zZ :: N -> N            -- L and Z (Z also sets r in C)
lL (P y _) = y
lL O = O                     -- C: L(0) = 0 (Z(0) diverges; never reached)
zZ (P _ x) = x
zZ O = error "Z 0"

bit1 :: N -> Bool            -- bit 1 of the number: tests u/2&1 and ~u&2
bit1 O = False
bit1 (P y x)
  | x == O = odd' y          -- 2y+1
  | x == P O O = True        -- (2y+1)*2
  | otherwise = False
  where odd' O = False
        odd' (P _ z) = z == O

small :: Integer -> N
small = fromI

-- S(v,y,c,t)
sL :: Integer -> N -> Integer -> N -> N
sL v y c t =
  let f = toI (lL t); x = zZ t in
  if f /= 2 then
    if f > 2 then (if f /= v then (if f > v then fromI (toI t - c) else t) else y)
    else P (fromI f) (P (sL v y c (lL x)) (sL (v + 2) (sL 4 (small 13) (-4) y) c (zZ x)))
  else aL (sL v y c (lL x)) (sL v y c (zZ x))

-- A(y,x)
aL :: N -> N -> N
aL y x = if toI (lL y) /= 1 then P (small 2) (P y x)  -- 5 << P(y,x)
         else sL 4 x 4 (zZ (zZ y))

shiftL :: N -> N
shiftL = sL 4 (small 13) (-4)

-- D(x); the stack a grows by one judgement P(t,P(u,P(x,c))) per call.
-- dL x returns that judgement and the pushes made, oldest first.
dL :: Integer -> (N, [N])
dL x0 = go x0 O (small 7) (small 14) []
 where
  go x c t u acc
    | x == 0 = done x c t u acc
    | otherwise =
        let (_, acc1) = dL (x - 1)
            x1 = x `div` 2
        in if odd x1 then body x1 c t u (acc ++ acc1) else done x1 c t u (acc ++ acc1)
  done x c t u acc = let j = P t (P u (P (fromI x) c)) in (j, acc ++ [j])
  rd x = let x' = x `div` 2 in (odd x', x')
  body x c t u acc =
    let (j, acc1) = dL x
        d = lL j; r1 = zZ j; f = lL r1; r2 = zZ r1
        xr = toI (lL r2); c' = zZ r2
        -- application and weakening, when the contexts agree
        (x3, t3, u3, c3) =
          if c /= c' then (xr, t, u, c)
          else
            let (x2, t2, u2) =
                  if lL u /= O then (xr, t, u)
                  else let r3 = zZ u in
                       if lL r3 /= f then (xr, t, u)
                       else let (b, xb) = rd xr in
                            if b then (xb, aL t d, sL 4 d 4 (zZ r3)) else (xb, t, u)
                (b, xb) = rd x2
            in if bit1 f && b then (xb, shiftL t2, shiftL u2, P d c) else (xb, t2, u2, c)
        -- abstraction or product over the last hypothesis
        (x4, t4, u4, c4) =
          if c3 == O then (x3, t3, u3, c3)
          else let (b, xb) = rd x3 in
               if not b then (xb, t3, u3, c3)
               else let (b2, xb2) = rd xb
                        hd = lL c3; tl = zZ c3
                    in if not (bit1 u3) || b2
                       then (xb2, P (small 1) (P hd t3), P O (P hd u3), tl)
                       else (xb2, P O (P hd t3), u3, tl)
        -- a variable of the type t, when t is a type
        (x5, t5, u5, c5) =
          let (b, xb) = rd x4 in
          if bit1 u4 && b then (xb, small 9, shiftL t4, P t4 c4) else (xb, t4, u4, c4)
    in go x5 c5 t5 u5 (acc ++ acc1)

------------------------------------------------------------------------
-- 2. Structured

data Tm = Star | Box | Tri | Var Int | Pi Tm Tm | Lam Tm Tm | App Tm Tm
  deriving (Eq, Ord, Show)

-- the codes of loader.c: tags 0 Pi, 1 Lam, 2 App, 3 sort, 4+2i variable i
enc :: Tm -> N
enc Star = small 7
enc Box = small 14
enc (Var i) = P (fromI (4 + 2 * fromIntegral i)) O
enc (Pi a b) = P O (P (enc a) (enc b))
enc (Lam a b) = P (small 1) (P (enc a) (enc b))
enc (App f d) = P (small 2) (P (enc f) (enc d))

-- sub v y c t: replace variable v by y; above v, i |-> i - c.
-- c = 1: beta (instantiate, close the gap); c = -1: shift.
sub :: Int -> Tm -> Int -> Tm -> Tm
sub v y c t = case t of
  Var i | i == v -> y
        | i > v -> Var (i - c)
        | otherwise -> t
  Pi a b -> Pi (sub v y c a) (sub (v + 1) (shift y) c b)
  Lam a b -> Lam (sub v y c a) (sub (v + 1) (shift y) c b)
  App f d -> app (sub v y c f) (sub v y c d)
  _ -> t

shift :: Tm -> Tm
shift = sub 0 (Var 1) (-1)

-- application of normal forms (hereditary: beta and renormalise)
app :: Tm -> Tm -> Tm
app (Lam _ b) d = sub 0 d 1 b
app f d = App f d

isSort :: Tm -> Bool
isSort s = s == Star || s == Box || s == Tri

-- a judgement  ctx |- tm : ty ; the context is innermost first
data J = J { ctx :: [Tm], tm :: Tm, ty :: Tm, rest :: Integer, calls :: [Integer] } deriving Show

-- the machine: the bits of x, read from bit 1 upwards, choose the rules.
-- Each D(x - 1) call of loader.c only pushes on the stack; it is kept
-- in dS for the comparison, and absent from derive.
derive :: (Integer -> J) -> Integer -> J
derive sub0 x0 = go x0 [] Star Box []
 where
  go x c t u cs
    | x == 0 = J c t u x cs
    | otherwise = let x1 = x `div` 2 in
                  if odd x1 then step x1 c t u (cs ++ [x - 1, x1]) else J c t u x1 (cs ++ [x - 1])
  rd x = let x' = x `div` 2 in (odd x', x')
  step x c t u cs =
    let J c' d f xr _ = sub0 x
        (x3, t3, u3, c3)
          | c /= c' = (xr, t, u, c)
          | otherwise =
              let (x2, t2, u2) = case u of
                    Pi a b | a == f -> let (bb, xb) = rd xr in
                                       if bb then (xb, app t d, sub 0 d 1 b) else (xb, t, u)
                    _ -> (xr, t, u)
                  (bb, xb) = rd x2
              in if isSort f && bb then (xb, shift t2, shift u2, d : c)    -- weakening
                 else (xb, t2, u2, c)
        (x4, t4, u4, c4) = case c3 of
          [] -> (x3, t3, u3, c3)
          (a : tl) ->
            let (bb, xb) = rd x3 in
            if not bb then (xb, t3, u3, c3)
            else let (b2, xb2) = rd xb in
                 if not (isSort u3) || b2
                 then (xb2, Lam a t3, Pi a u3, tl)                         -- abstraction
                 else (xb2, Pi a t3, u3, tl)                               -- product
        (x5, t5, u5, c5) =
          let (bb, xb) = rd x4 in
          if isSort u4 && bb then (xb, Var 0, shift t4, t4 : c4)          -- variable
          else (xb, t4, u4, c4)
    in go x5 c5 t5 u5 cs

-- memoised: the judgement of x depends only on x
judgements :: Integer -> M.Map Integer J
judgements n = m
  where m = M.fromList [ (x, derive (m M.!) x) | x <- [0 .. n] ]

encJ :: J -> N
encJ (J c t u x _) = P (enc t) (P (enc u) (P (fromI x) (foldr (\a r -> P (enc a) r) O c)))

-- the stack of loader.c, from the structured machine: the pushes of the
-- recursive calls in order, then the judgement itself
stackS :: M.Map Integer J -> Integer -> [N]
stackS m x = let j = m M.! x in concatMap (stackS m) (calls j) ++ [encJ j]

------------------------------------------------------------------------
-- 3. An independent checker for CC (PTS with * : [], rules (s1,s2,s2)),
-- with conversion by full normalisation (substitution, not hereditary).

up :: Int -> Int -> Tm -> Tm          -- up k d: indices >= k move by d
up k d t = case t of
  Var i -> if i >= k then Var (i + d) else t
  Pi a b -> Pi (up k d a) (up (k + 1) d b)
  Lam a b -> Lam (up k d a) (up (k + 1) d b)
  App f e -> App (up k d f) (up k d e)
  _ -> t

subst :: Int -> Tm -> Tm -> Tm        -- t[s/k], closing the gap
subst k s t = case t of
  Var i | i == k -> up 0 k s
        | i > k -> Var (i - 1)
        | otherwise -> t
  Pi a b -> Pi (subst k s a) (subst (k + 1) s b)
  Lam a b -> Lam (subst k s a) (subst (k + 1) s b)
  App f e -> App (subst k s f) (subst k s e)
  _ -> t

nf :: Tm -> Tm
nf t = case t of
  Pi a b -> Pi (nf a) (nf b)
  Lam a b -> Lam (nf a) (nf b)
  App f e -> case nf f of
    Lam _ b -> nf (subst 0 e b)
    f' -> App f' (nf e)
  _ -> t

type Ctx = [Tm]

-- ext: also Box : Tri (one more universe, as in CC with universes, LICS 1986); rules (s1,s2,s2)
-- for all sorts
infer :: Bool -> Ctx -> Tm -> Either String Tm
infer ext g t = case t of
  Star -> Right Box
  Box -> if ext then Right Tri else Left "Box has no type"
  Tri -> Left "Tri has no type"
  Var i -> if i < length g then Right (up 0 (i + 1) (g !! i)) else Left "unbound"
  Pi a b -> do _ <- sortOf ext g a; sortOf ext (a : g) b
  Lam a b -> do _ <- sortOf ext g a; bt <- infer ext (a : g) b
                _ <- sortOf ext g (Pi a bt)
                Right (Pi a bt)
  App f e -> do
    ft <- infer ext g f
    case nf ft of
      Pi a b -> do et <- infer ext g e
                   if nf a == nf et then Right (subst 0 e b) else Left "argument type"
      _ -> Left "not a function"

sortOf :: Bool -> Ctx -> Tm -> Either String Tm
sortOf ext g a = do
  s <- infer ext g a
  let s' = nf s
  if isSort s' then Right s' else Left "not a type"

wfCtx :: Bool -> Ctx -> Either String ()
wfCtx _ [] = Right ()
wfCtx ext (a : g) = wfCtx ext g >> sortOf ext g a >> Right ()

checkJ :: Bool -> J -> Either String ()
checkJ ext (J c t u _ _) = do
  wfCtx ext c
  u' <- infer ext c t
  if nf u' /= u then Left "type differs" else Right ()
  if nf t /= t then Left "term not normal" else Right ()

------------------------------------------------------------------------

size :: Tm -> Int
size t = case t of
  Pi a b -> 1 + size a + size b
  Lam a b -> 1 + size a + size b
  App f e -> 1 + size f + size e
  _ -> 1

main :: IO ()
main = do
  args <- getArgs
  let (nLit, nStr) = case args of
        [a, b] -> (read a, read b)
        _ -> (12, 4096)
  -- (1) = (2): the judgement of each x, and the whole stack for small x
  let m = judgements nStr
      agree = and [ dL x == (encJ (m M.! x), stackS m x) | x <- [0 .. nLit] ]
  putStrLn ("literal = structured (judgement and whole stack) on x <= " ++ show nLit ++ ": " ++ show agree)
  -- (3) every judgement checks
  let js = M.toList m
      bad = [ (x, e, j) | (x, j) <- js, Left e <- [checkJ False j] ]
      badExt = [ (x, e, j) | (x, j) <- js, Left e <- [checkJ True j] ]
      distinct = M.size (M.fromList [ ((ctx j, tm j, ty j), ()) | (_, j) <- js ])
      big = maximum [ size (tm j) | (_, j) <- js ]
  putStrLn ("judgements x <= " ++ show nStr ++ ": " ++ show (length js)
            ++ " (distinct " ++ show distinct ++ "), largest term " ++ show big)
  putStrLn ("rejected by the CC checker: " ++ show (length bad))
  mapM_ (\(x, e, j) -> putStrLn ("  x = " ++ show x ++ ": " ++ e ++ "  " ++ show j)) (take 3 bad)
  let kinds = M.keys (M.fromList [ ((tm j, ty j), ()) | (_, _, j) <- bad ])
  putStrLn ("  distinct (term, type) rejected: " ++ show kinds)
  putStrLn ("rejected by CC + (Box : Tri): " ++ show (length badExt))
  mapM_ (\(x, e, j) -> putStrLn ("  x = " ++ show x ++ ": " ++ e ++ "  " ++ show j)) (take 3 badExt)
