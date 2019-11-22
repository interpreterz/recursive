import Data.List
import System.IO
import qualified Data.Map as Map


data Value =
  Numv  Float  |
  Boolv Bool   |
  Procv Env [Ast] Ast |
  Recuv Env Env [Ast] Ast
  deriving (Eq)

instance Show Value where
  show (Numv x)  = show x
  show (Boolv x) = show x
  show (Procv _ _ _) = "#<procedure>"
  show (Recuv _ _ _ _) = "#<procedure>"

instance Num Value where
  (Numv x) + (Numv y) = Numv $ x + y
  (Numv x) * (Numv y) = Numv $ x * y
  abs (Numv x)    = Numv $ abs x
  signum (Numv x) = Numv $ signum x
  fromInteger x   = Numv $ fromInteger x
  negate (Numv x) = Numv $ negate x

instance Fractional Value where
  (Numv x) / (Numv y) = Numv $ x / y
  fromRational x = Numv $ fromRational x


data Ast =
  Numa   Float   |
  Boola  Bool    |
  Ida    String  |
  Primv  String  |
  Ifte      Ast Ast Ast      |
  Assume    [(Ast, Ast)] Ast |
  Function  [Ast] Ast        |
  Recfun    [(Ast, [Ast], Ast)] Ast |
  Apply     Ast [Ast]
  deriving (Eq, Read, Show)

type Env = Map.Map String Value

main = do
  putStr "recursive: "
  hFlush stdout
  exp <- getLine
  if null exp
    then return ()
    else do
      putStrLn (show . run $ exp)
      main

run :: String -> Value
run = (eval $ Map.fromList def) . parse
  where def = map f ops
        f s = (s, Procv m fs $ Primv s)
        ops = ["+", "*", "-", "/", "=", "&", "|", "~", "zero?"]
        fs = [Ida "x", Ida "y"]
        m = Map.empty

eval :: Env -> Ast -> Value
eval _ (Numa  x) = Numv  x
eval _ (Boola x) = Boolv x
eval m (Ida x)   = get m x
eval m (Primv "+") = (get m "x") + (get m "y")
eval m (Primv "*") = (get m "x") * (get m "y")
eval m (Primv "-") = (get m "x") - (get m "y")
eval m (Primv "/") = (get m "x") / (get m "y")
eval m (Primv "=") = Boolv $ get m "x" == get m "y"
eval m (Primv "&") = Boolv $ get m "x" == Boolv True && get m "y" == Boolv True
eval m (Primv "|") = Boolv $ get m "x" == Boolv True || get m "y" == Boolv True
eval m (Primv "~") = Boolv $ if get m "x" == Boolv True then False else True
eval m (Primv "zero?")  = Boolv $ get m "x" == Numv 0
eval m (Ifte c t e)     = if eval m c == Boolv True then eval m t else eval m e
eval m (Assume bs x)    = eval m' x
  where m' = Map.union mb m
        mb = elaborate m bs
eval m (Function fs b)  = Procv m fs b
eval m (Recfun ps x) = eval m' x
  where m' = Map.union mb m
        mb = recurse . elaborate m . map f $ ps
        f (l, fs, b) = (l, Function fs b)
eval m (Apply x ps)     = eval m' b
  where m' = Map.union mf ml
        mf = elaborate m $ zip fs ps
        (Procv ml fs b) = unrecurse $ eval m x

unrecurse :: Value -> Value
unrecurse (Recuv m mb fs b) = Procv m' fs b
  where m' = Map.union (recurse mb) m
unrecurse v = v

recurse :: Env -> Env
recurse mb = Map.map f mb
  where f (Procv m fs b) = Recuv m mb fs b
        f x = x

elaborate :: Env -> [(Ast, Ast)] -> Env
elaborate m =  Map.fromList . map f
  where f (Ida x, e) = (x, eval m e)

get :: Env -> String -> Value
get m id = case v of
    (Just x) -> x
    Nothing  -> error $ "id " ++ id ++ " not set!"
  where v = Map.lookup id m


parse :: String -> Ast
parse s = (read . unwords . unpack . alter . Bnode "" . pack . words $ bpad) :: Ast
  where bpad = replace "(" " ( " . replace ")" " ) " . replace "[" "(" . replace "]" ")" $ s

alter :: Btree -> Btree
alter (Bnode _ (Bleaf "ifte":ns)) = (Bnode "(" (Bleaf "Ifte":ns'))
  where ns' = map alter ns
alter (Bnode _ (Bleaf "assume":Bnode _ bs:e)) = (Bnode "(" (Bleaf "Assume":Bnode "[" bs':e'))
  where e' = map alter e
        bs' = intersperse c . map pair $ bs
        pair (Bnode _ xv) = Bnode "(" . intersperse c . map alter $ xv
        c = Bleaf ","
alter (Bnode _ (Bleaf "function":Bnode _ fs:b)) = (Bnode "(" (Bleaf "Function":Bnode "[" fs':b'))
  where b' = map alter b
        fs' = intersperse c . map alter $ fs
        c = Bleaf ","
alter (Bnode _ (Bleaf "recfun":Bnode _ ps:e)) = (Bnode "(" (Bleaf "Recfun":Bnode "[" ps':e'))
  where e' = map alter e
        ps' = intersperse c . map proc $ ps
        proc (Bnode _ (l:Bnode _ fs:b)) = Bnode "(" . intersperse c $ l':(Bnode "[" fs'):b'
          where (l', b') = (alter l, map alter b)
                fs' = intersperse c . map alter $ fs
        c = Bleaf ","
alter (Bnode _ (Bleaf "@":e:ps)) = (Bnode "(" (Bleaf "Apply":e':ps'))
  where e' = alter e
        ps' = [Bnode "[" . intersperse c . map alter $ ps]
        c = Bleaf ","
alter (Bnode "(" ns) = alter $ Bnode "(" $ Bleaf "@":ns
alter (Bnode b ns) = Bnode b $ map alter ns
alter (Bleaf w) = Bleaf $ case w of
  w
    | isFloat w  -> "(Numa "  ++ w ++ ")"
    | isBool  w  -> "(Boola " ++ w ++ ")"
    | otherwise  -> "(Ida \""   ++ w ++ "\")"


data Btree =
  Bnode String [Btree] |
  Bleaf String
  deriving (Eq, Read, Show)

unpack :: Btree -> [String]
unpack (Bleaf w)  = [w]
unpack (Bnode b ns) = b : (foldr (++) [b'] $ map unpack ns)
  where b' = if b == "[" then "]" else (if b == "(" then ")" else "")

pack :: [String] -> [Btree]
pack [] = []
pack all@(w:ws)
  | isClose = []
  | isOpen  = node : pack ws'
  | otherwise = Bleaf w : pack ws
  where isOpen  = w == "[" || w == "("
        isClose = w == "]" || w == ")"
        node = Bnode w $ pack ws
        ws' = drop (area node) all
        win = pack ws

area :: Btree -> Int
area (Bleaf _) = 1
area (Bnode _ ns) = foldr (+) 2 $ map area ns


replace :: (Eq a) => [a] -> [a] -> [a] -> [a]
replace _ _ [] = []
replace from to all@(x:xs)
  | from `isPrefixOf` all = to ++ (replace from to . drop (length from) $ all)
  | otherwise             = x : replace from to xs

isFloat :: String -> Bool
isFloat s = case (reads s) :: [(Float, String)] of
  [(_, "")] -> True
  _         -> False

isBool :: String -> Bool
isBool s = case (reads s) :: [(Bool, String)] of
  [(_, "")] -> True
  _         -> False
