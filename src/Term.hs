-- Term.hs -- strict positivity of data types: a syntactic pass over the
-- resolved units, after resolution and before filling and checking,
-- without evaluation.
--
-- Recursion is only by eliminators and the scope is sequential (SegParse),
-- so no termination check is needed.  In a constructor field, the data
-- types of the group may occur only strictly positively: never in the
-- domain of a function type, and never as an argument of another type (no
-- nested types); a field mentions its data type only with its uniform
-- parameters (PRIMREC.md 2).  Enforced by the resolver and inside #fails.

module Term (positivityReport, termErrors) where

import Seg
import qualified Data.Set as Set

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

------------------------------------------------------------------------
-- Enforcement: the errors of the units  part  of the program  whole

termErrors :: [Unit] -> [Unit] -> [String]
termErrors _ part = positivityReport part

