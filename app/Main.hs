{-# LANGUAGE ScopedTypeVariables #-}
-- seg file.seg [+id | -id | --none | -v]...
--
-- Parses, expands imports, resolves and checks a file.  Each declaration
-- has a budget of ten seconds; an overrun is reported as a failure, with
-- the name of the declaration.  The lock strategy is a property of the
-- run (Wang, final.pdf): +id locks id and -id unlocks it on top of what
-- the file declares, --none ignores the file's locks.
--
-- import F ;  splices the file F.seg (same directory) as  module F { .. }.
-- A file is imported once; later imports of it are dropped.

module Main where

import Seg
import SegParse
import System.Environment (getArgs, lookupEnv)
import System.Timeout (timeout)
import System.Exit (exitFailure)
import System.IO (isEOF, hFlush, hClose, stdout, openFile, IOMode(..), hPutStrLn, stderr)
import GHC.IO.Handle (hDuplicate, hDuplicateTo)
import System.Directory (listDirectory, getModificationTime, renameFile, removeFile,
                         createDirectoryIfMissing)
import Control.Concurrent (threadDelay)
import Control.Monad (forM, when, unless)
import qualified Data.Set as Set
import Data.Char (isAlphaNum)
import Data.List (isPrefixOf, isSuffixOf, sort)
import Control.Exception (evaluate, try, ErrorCall(..), IOException)
import Data.IORef
import Data.List (nub)
import System.CPUTime (getCPUTime)
import qualified Data.Map.Strict as Map
import Data.List (sortBy)
import Data.Ord (comparing, Down(..))
import Text.Printf (printf)

budget :: Int
budget = 10000000

data Opt = Opt { oOn :: [Id], oOff :: [Id], oNone :: Bool, oVerbose :: Bool
               , oOnly :: [String], oOnlyTop :: [String], oUnfolds :: Bool, oEach :: Bool, oRepl :: Bool
               , oServe :: Maybe FilePath }

-- --only M  (repeatable): check only the declarations of module M (any
-- module whose path has a component M); everything else is TRUSTED: it is
-- entered into the context (lazily) but its proofs are not checked.  The
-- context after a declaration never depends on whether it checked, so this
-- is Agda's separate checking of modules, with no cache to keep coherent.
-- --only-top M  (repeatable): only the declarations directly in M, not in
-- the modules nested in M (a segment whose files are imported inside it).
opts :: [String] -> Opt
opts = go (Opt [] [] False False [] [] False False False Nothing)
 where
  go o [] = o
  go o ("--only" : m : rest) = go o { oOnly = m : oOnly o } rest
  go o ("--only-top" : m : rest) = go o { oOnlyTop = m : oOnlyTop o } rest
  go o ("--serve" : d : rest) = go o { oServe = Just d } rest
  go o (a : rest) = go (add a o) rest
  add "--none" o = o { oNone = True }
  add "--unfolds" o = o { oUnfolds = True }
  add "--each" o = o { oEach = True }
  add "--repl" o = o { oRepl = True }
  add "-v" o = o { oVerbose = True }
  add ('+' : x) o = o { oOn = x : oOn o }
  add ('-' : x) o = o { oOff = x : oOff o }
  add _ o = o

-- the most unfolded constants, with their counts
topUnfolds :: Int -> Map.Map Id Int -> String
topUnfolds k m = unwords [ shortId i ++ ":" ++ show c
                         | (i, c) <- take k (sortBy (comparing (Down . snd)) (Map.toList m)) ]

splitDots :: String -> [String]
splitDots s = case break (== '.') s of
  (a, [])       -> [a]
  (a, _ : rest) -> a : splitDots rest

main :: IO ()
main = do
  args <- getArgs
  case args of
    (f : rest) -> runFile f (opts rest)
    [] -> putStrLn "usage: seg file.seg [+id] [-id] [--none] [-v]"

dirOf :: FilePath -> FilePath
dirOf p = reverse (dropWhile (/= '/') (reverse p))

-- expand imports, depth first, each file once
expand :: IORef [String] -> FilePath -> [RUnit] -> IO [RUnit]
expand seen dir = fmap concat . mapM go
 where
  go u = case u of
    RImport x -> do
      s <- readIORef seen
      if x `elem` s then return [] else do
        modifyIORef seen (x :)
        src <- readFile (dir ++ x ++ ".seg")
        case parseUnits src of
          Left msg -> error ("in " ++ x ++ ".seg: " ++ msg)
          Right us -> do
            us' <- expand seen dir us
            return [RModule x [] us']
    RModule x tel us -> do us' <- expand seen dir us
                           return [RModule x tel us']
    _ -> return [u]

adjust :: Opt -> [Unit] -> [Unit]
adjust o us = ULock (fix []) : map go us
 where
  fix s = nub (oOn o ++ filter (`notElem` oOff o) (if oNone o then [] else s))
  go u = case u of
    ULock s -> ULock (fix s)
    UMod i x mus d -> UMod i x (map go mus) d
    _ -> u

-- parse, expand imports, resolve: the program's units, and the modules
-- imported by the file (in order) for --each
loadProgram :: FilePath -> Opt -> IO (Either String ([Unit], [String]))
loadProgram f o = fmap (fmap (\(us, mods, _) -> (us, mods))) (loadFiles f o)

-- the same, with every file spliced in, at any depth, in import order
loadFiles :: FilePath -> Opt -> IO (Either String ([Unit], [String], [String]))
loadFiles f o = do
  src <- readFile f
  let self = baseName f
  seen <- newIORef [self]
  case parseUnits src of
    Left msg -> return (Left ("PARSE ERROR\n" ++ msg))
    Right us0 -> do
      rus <- expand seen (dirOf f) us0
      files <- fmap (filter (/= self) . reverse) (readIORef seen)
      case resolveProgram rus of
        Left msg -> return (Left ("SCOPE ERROR\n" ++ msg))
        Right us -> return (Right (adjust o us, importsOf us0, files))
 where
  importsOf us = concatMap imp us
  imp u = case u of
    RImport x -> [x]
    RModule _ _ vs -> importsOf vs
    _ -> []

-- check the given events (each with the ten-second budget); prints the
-- failures and outputs; returns (declarations, failures)
runEvents :: Opt -> IORef (Map.Map Id Int) -> [Event] -> IO (Int, Int)
runEvents o total evs = do
  failures <- newIORef (0 :: Int)
  count <- newIORef (0 :: Int)
  mapM_ (\e -> do
           writeIORef unfoldCount Map.empty
           t1 <- getCPUTime
           r <- timeout budget (try (evaluate (forceRes (evResult e))))
           t2 <- getCPUTime
           let secs = fromIntegral (t2 - t1) / 1e12 :: Double
           if oUnfolds o then do
               m <- readIORef unfoldCount
               modifyIORef' total (Map.unionWith (+) m)
               if secs > 0.3 then putStrLn ("  unfolds in " ++ evLabel e ++ printf " (%.2f s): " secs
                                            ++ printf "[%d total, %d distinct] " (sum (Map.elems m)) (Map.size m)
                                            ++ topUnfolds 14 m) else return ()
             else return ()
           modifyIORef count (+1)
           case r of
             Nothing -> do modifyIORef failures (+1)
                           putStrLn ("OVERRUN (10 s): " ++ evLabel e)
             Just (Left (ErrorCall m)) -> do
               modifyIORef failures (+1)
               putStrLn ("INTERNAL ERROR in " ++ evLabel e ++ ": " ++ m)
             Just (Right (Left msg)) -> do
               modifyIORef failures (+1)
               putStrLn ("FAILED: " ++ evLabel e ++ "\n" ++ indent msg)
             Just (Right (Right out)) -> do
               mapM_ putStrLn out
               if oVerbose o || secs > 1 then printf "  %-40s %.3f s\n" (evLabel e) secs else return ()
        ) evs
  c <- readIORef count
  n <- readIORef failures
  return (c, n)
 where
  indent = unlines . map ("  " ++) . lines
  forceRes r = case r of
    Left m   -> length m `seq` r
    Right xs -> sum (map length xs) `seq` r

-- the events of module m (any module whose path has the component m)
inModule :: String -> Event -> Bool
inModule m e = m `elem` splitDots (evLabel e)

-- directly in M: M is the module of the declaration itself
inModuleTop :: String -> Event -> Bool
inModuleTop m e = case reverse (splitDots (evLabel e)) of
  (_ : p : _) -> p == m
  _ -> False

secsSince :: Integer -> IO Double
secsSince t0 = do t <- getCPUTime; return (fromIntegral (t - t0) / 1e12)

runFile :: FilePath -> Opt -> IO ()
runFile f o
  | Just d <- oServe o = serve f d o
  | oRepl o = repl f o
  | otherwise = do
  t0 <- getCPUTime
  loaded <- loadProgram f o
  (us, mods) <- case loaded of
    Left msg -> do putStrLn msg; exitFailure
    Right x -> return x
  let (_, evs0) = checkUnits emptyCx us
  tl <- secsSince t0
  if oVerbose o then printf "  (parse, resolve: %.3f s)\n" tl else return ()
  writeIORef unfoldOn (oUnfolds o)
  dist <- lookupEnv "SEG_DISTINCT"
  writeIORef distinctOn (dist /= Nothing)
  total <- newIORef (Map.empty :: Map.Map Id Int)
  if oEach o
    then do
      -- every imported module, one at a time, in one process: the parsed
      -- port and everything already evaluated are shared between modules
      results <- mapM (\m -> do
                         t1 <- getCPUTime
                         (c, n) <- runEvents o total (filter (inModule m) evs0)
                         dt <- secsSince t1
                         printf "%-4s  %-18s %4d declarations  %6.2f s\n" (if n == 0 then "ok" else "FAIL") m c dt
                         return n) mods
      tt <- secsSince t0
      let bad = length (filter (> 0) results)
      printf "%s: %d modules, %d with failures, %.2f s in all (load %.2f s)\n" f (length mods) bad tt tl
      if bad > 0 then exitFailure else putStrLn "OK"
    else do
      let noSel = null (oOnly o) && null (oOnlyTop o)
          selected e = noSel || any (\m -> inModule m e) (oOnly o) || any (\m -> inModuleTop m e) (oOnlyTop o)
      (c, n) <- runEvents o total (filter selected evs0)
      if oUnfolds o then do
          m <- readIORef total
          putStrLn ("unfolds, whole run: " ++ topUnfolds 15 m)
        else return ()
      tt <- secsSince t0
      let pns = [ x | UPar _ x _ <- us ]
      printf "%s: %d declarations%s, %d failed, %.2f s\n" f c
             (if noSel then "" else " (" ++ unwords (oOnly o ++ oOnlyTop o) ++ "; the rest trusted)") n tt
      if null pns then return () else putStrLn ("assuming: " ++ unwords pns)
      if n > 0 then exitFailure else putStrLn "OK"

-- A session: the program is loaded once and kept; commands are read from
-- standard input (a terminal, or a script piped in):
--   check M [M ..]   check these modules, the rest trusted
--   each             every imported module, one at a time
--   reload           re-read the files (after editing them)
--   quit
-- What has been evaluated stays evaluated until the next reload.
repl :: FilePath -> Opt -> IO ()
repl f o = do
  st <- newIORef Nothing
  total <- newIORef (Map.empty :: Map.Map Id Int)
  writeIORef unfoldOn (oUnfolds o)
  let load = do
        t0 <- getCPUTime
        r <- loadProgram f o
        dt <- secsSince t0
        case r of
          Left msg -> do putStrLn msg; writeIORef st Nothing
          Right (us, mods) -> do
            let (_, evs) = checkUnits emptyCx us
            writeIORef st (Just (evs, mods))
            printf "loaded %s: %d modules (%.2f s)\n" f (length mods) dt
      run ms = do
        s <- readIORef st
        case s of
          Nothing -> putStrLn "nothing loaded (reload)"
          Just (evs, _) -> mapM_ (\m -> do
              t1 <- getCPUTime
              (c, n) <- runEvents o total (filter (inModule m) evs)
              dt <- secsSince t1
              printf "%-4s  %-18s %4d declarations  %6.2f s\n" (if n == 0 then "ok" else "FAIL") m c dt) ms
      loop = do
        eof <- isEOF
        if eof then return () else do
          l <- getLine
          case words l of
            ["quit"] -> return ()
            ["reload"] -> load >> loop
            ("check" : ms) -> run ms >> loop
            ["each"] -> do s <- readIORef st
                           case s of
                             Just (_, mods) -> run mods
                             Nothing -> putStrLn "nothing loaded (reload)"
                           loop
            [] -> loop
            _ -> do putStrLn "commands: check M .. | each | reload | quit"; loop
  load
  loop

baseName :: FilePath -> String
baseName f = takeWhile (/= '.') (reverse (takeWhile (/= '/') (reverse f)))

------------------------------------------------------------------------
-- The checking server: the program is loaded once and kept in memory;
-- requests come as files in a directory, so any number of clients (the
-- shell script segc) can use it.
--
--   seg All.seg --serve DIR
--
-- A client writes DIR/req.<id> (one command line) and waits for
-- DIR/resp.<id>.  Before each command the server compares the
-- modification times of the .seg files with those of the last load; if
-- one changed it reloads (parse and resolve only: evaluation is lazy) and
-- marks the changed files DIRTY.  Commands:
--   check M ..   these file-modules
--   changed      the dirty files and every file depending on them
--   all          every file-module, in import order (the full check)
--   deps M ..    the files depending on M .. (no check)
--   status | reload | quit
-- A file-module is a file spliced by import, at any depth; its
-- declarations are those whose innermost enclosing file is that file.
-- A module FAILs if a declaration fails or overruns its ten seconds, or
-- if the module takes ten seconds or more in all.
-- Dependencies: F depends on G if F's text (comments and import lines
-- removed) mentions G as a word, or F is a file whose imports include G's
-- dependents' container; transitively.  This over-approximates the use
-- of G, since a file refers to another one only through its name.

data Srv = Srv { sEvs :: [Event], sFiles :: [String], sMain :: String
               , sStamps :: Map.Map FilePath String, sDirty :: Set.Set String
               , sToks :: Map.Map String (Set.Set String), sNested :: Map.Map String [String]
               , sKeys :: Map.Map String String }

serve :: FilePath -> FilePath -> Opt -> IO ()
serve f dir o = do
  createDirectoryIfMissing True dir
  writeIORef unfoldOn (oUnfolds o)
  -- the baseline: the files and their contents at the last good check
  -- (changed or all), kept on disk so that a new server knows it; without
  -- one, every file is dirty
  base <- readBaseline
  let (files0, keys0) = maybe ([], Map.empty) id base
  st <- newIORef (Srv [] files0 (baseName f) Map.empty Set.empty Map.empty Map.empty keys0)
  _ <- reload st
  hPutStrLn stderr ("seg server: " ++ f ++ " in " ++ dir)
  let loop = do
        reqs <- fmap (sort . filter (\x -> "req." `isPrefixOf` x && not (".tmp" `isSuffixOf` x)))
                     (listDirectory dir)
        case reqs of
          [] -> threadDelay 50000 >> loop
          (r : _) -> do
            let p = dir ++ "/" ++ r
                rid = drop 4 r
            cmd <- readFile p
            length cmd `seq` removeFile p
            let tmp = dir ++ "/resp." ++ rid ++ ".tmp"
            h <- openFile tmp WriteMode
            hFlush stdout
            old <- hDuplicate stdout
            hDuplicateTo h stdout
            continue <- (command st (words cmd)) `catchAll` (\m -> putStrLn ("SERVER ERROR: " ++ m) >> return True)
            hFlush stdout
            hDuplicateTo old stdout
            hClose h
            renameFile tmp (dir ++ "/resp." ++ rid)
            if continue then loop else return ()
  loop
 where
  catchAll act k = do
    r <- try act
    case r of
      Left (ErrorCall m) -> k m
      Right x -> return x

  sources = do
    xs <- listDirectory (dirOf' f)
    let segs = [ x | x <- xs, ".seg" `isSuffixOf` x ]
    fmap Map.fromList (forM segs (\x -> do
      t <- getModificationTime (dirOf' f ++ x)
      return (x, show t)))

  -- reload; the files whose text changed (comments and import lines
  -- aside), the new files, the files whose predecessors changed, and the
  -- removed files become dirty
  reload st = do
    t0 <- getCPUTime
    stamps <- sources
    r <- loadFiles f o
    dt <- secsSince t0
    case r of
      Left msg -> do putStrLn msg
                     modifyIORef st (\s -> s { sEvs = [], sStamps = stamps })
                     return False
      Right (us, _, files) -> do
        texts <- forM (files ++ [baseName f]) (\x -> do
          src <- readFile (dirOf' f ++ x ++ ".seg")
          length src `seq` return (x, src))
        old <- readIORef st
        let (_, evs) = checkUnits emptyCx us
            toks = Map.fromList [ (x, tokens src) | (x, src) <- texts ]
            nested = Map.fromList [ (x, importsIn src) | (x, src) <- texts ]
            keys = Map.fromList [ (x, contentKey src) | (x, src) <- texts ]
            oldFiles = sFiles old
            first = Map.null (sKeys old)
            textChanged = [ x | (x, k) <- Map.toList keys, Map.lookup x (sKeys old) /= Just k ]
            removed = [ x | x <- oldFiles, x `notElem` files ]
            before xs = Map.fromList (zip xs (scanl (flip Set.insert) Set.empty xs))
            preOld = before oldFiles
            preNew = before files
            moved = [ y | y <- files, Just po <- [Map.lookup y preOld], Just pn <- [Map.lookup y preNew]
                        , not (Set.null (Set.difference po pn))
                          || any (`elem` oldFiles) (Set.toList (Set.difference pn po)) ]
            dirty = if first then files else nub (textChanged ++ moved ++ removed)
        unless (null dirty) (putStrLn ("dirty: " ++ unwords dirty))
        modifyIORef st (\s -> s { sEvs = evs, sFiles = files, sStamps = stamps
                                , sDirty = Set.union (Set.fromList dirty) (sDirty s)
                                , sToks = toks, sNested = nested, sKeys = keys })
        printf "loaded %s: %d files (%.2f s)\n" f (length files) dt
        return True

  baselineFile = dir ++ "/good"
  readBaseline = do
    r <- try (readFile baselineFile >>= \t -> length t `seq` return t)
    return (case r of
      Left (_ :: IOException) -> Nothing
      Right t -> case reads t of
        [(b, _)] -> Just (b :: ([String], Map.Map String String))
        _ -> Nothing)
  markGood st = do
    modifyIORef st (\s' -> s' { sDirty = Set.empty })
    s' <- readIORef st
    writeFile (baselineFile ++ ".tmp") (show (sFiles s', sKeys s'))
    renameFile (baselineFile ++ ".tmp") baselineFile

  -- reload if a file's modification time changed since the last load
  fresh st = do
    s <- readIORef st
    stamps <- sources
    if stamps == sStamps s && not (null (sEvs s)) then return True else reload st

  command st ws = case ws of
    ["quit"] -> putStrLn "bye" >> return False
    ["reload"] -> reload st >> return True
    ["status"] -> do
      _ <- fresh st
      s <- readIORef st
      printf "%d files, %d declarations; dirty: %s\n" (length (sFiles s)) (length (sEvs s))
             (unwords (Set.toList (sDirty s)))
      return True
    ("deps" : ms) -> do
      ok <- fresh st
      when ok (do s <- readIORef st
                  putStrLn (unwords (closure s ms)))
      return True
    ("check" : ms) -> do
      ok <- fresh st
      when ok (do s <- readIORef st
                  _ <- runMods st [ m | m <- sFiles s ++ [sMain s], m `elem` ms ]
                  return ())
      return True
    ["changed"] -> do
      ok <- fresh st
      when ok (do s <- readIORef st
                  let seeds = Set.toList (sDirty s)
                  if null seeds then putStrLn "nothing changed\nOK" else do
                    let ms = closure s seeds
                    good <- runMods st ms
                    when good (markGood st))
      return True
    ["all"] -> do
      ok <- fresh st
      when ok (do s <- readIORef st
                  good <- runMods st (sFiles s ++ [sMain s])
                  when good (markGood st))
      return True
    _ -> do putStrLn "commands: check M .. | changed | all | deps M .. | status | reload | quit"
            return True

  -- check the file-modules ms (in import order); True if all are ok
  runMods st ms = do
    s <- readIORef st
    total <- newIORef Map.empty
    let fileSet = Set.fromList (sFiles s)
        owner e = case [ c | c <- init (splitDots (evLabel e)), c `Set.member` fileSet ] of
                    [] -> sMain s
                    cs -> last cs
        byFile = Map.fromListWith (flip (++)) [ (owner e, [e]) | e <- sEvs s ]
    t0 <- getCPUTime
    results <- forM ms (\m -> do
      t1 <- getCPUTime
      (c, n) <- runEvents o total (Map.findWithDefault [] m byFile)
      dt <- secsSince t1
      let bad = n > 0 || dt >= 10
      printf "%-4s  %-20s %4d declarations  %6.2f s%s\n" (if bad then "FAIL" else "ok") m c dt
             (if n == 0 && dt >= 10 then "  (over the 10 s cap)" else "")
      return bad)
    tt <- secsSince t0
    let nbad = length (filter id results)
    printf "%d modules, %d failed, %.2f s\n" (length ms) nbad tt
    putStrLn (if nbad == 0 then "OK" else "FAILED")
    return (nbad == 0)

  -- the files depending on the seeds, transitively, in import order
  closure s seeds =
    let files = sFiles s
        mentions x = [ y | y <- files, y /= x, x `Set.member` Map.findWithDefault Set.empty y (sToks s) ]
        inside x = Map.findWithDefault [] x (sNested s)
        go done [] = done
        go done (x : xs)
          | x `Set.member` done = go done xs
          | otherwise = go (Set.insert x done) (mentions x ++ inside x ++ xs)
        everything = any (== sMain s) seeds
        set = go Set.empty (concat [ if x `elem` files then [x] else mentions x | x <- seeds ])
    in if everything then files ++ [sMain s] else filter (`Set.member` set) files

  dirOf' p = case dirOf p of { "" -> "./"; d -> d }

-- the words of a text, comments and import lines removed; a qualified
-- name A.b gives A and b
tokens :: String -> Set.Set String
tokens src = Set.fromList (concatMap splitDots (words (map sep body)))
 where
  body = unlines [ l | l0 <- lines src, let l = stripComment l0
                     , not ("import " `isPrefixOf` dropWhile (== ' ') l) ]
  sep c = if isAlphaNum c || c `elem` "_'-." then c else ' '
  stripComment l = case l of
    [] -> []
    ('-' : '-' : _) -> []
    (c : cs) -> c : stripComment cs

-- what a change must alter to matter: the text without comments, import
-- lines and blank space at line ends
contentKey :: String -> String
contentKey src = unlines [ l | l0 <- lines src
                             , let l = reverse (dropWhile (== ' ') (reverse (stripC l0)))
                             , not (null l), not ("import " `isPrefixOf` dropWhile (== ' ') l) ]
 where stripC l = case l of
         [] -> []
         ('-' : '-' : _) -> []
         (c : cs) -> c : stripC cs

-- the files imported in a text (its nested files)
importsIn :: String -> [String]
importsIn src = [ takeWhile (\c -> isAlphaNum c || c == '_') (drop 7 l)
                | l0 <- lines src, let l = dropWhile (== ' ') l0, "import " `isPrefixOf` l ]
