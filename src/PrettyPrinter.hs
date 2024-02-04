module PrettyPrinter where

import Syntax
import Control.Monad.State
import qualified Data.Map as M
import Control.Monad.RWS (All(getAll))

addParens :: String -> String
addParens s = "(" ++ s ++ ")"

class MyPrinter a where
  printt :: a -> String

-- ideally, we only need printt to show the results
instance MyPrinter Value where
  printt v = case v of
    Var x _ -> x
    Lam x c -> "\\ " ++ x ++ " . " ++ printt c
    Vunit   -> "unit"
    Vpair (v1, v2) -> "(" ++ printt v1 ++ ", " ++ printt v2 ++ ")"
    Vhandler h -> printt h
    Vbool b -> if b then "true" else "false"
    Vint n -> show n
    Vchar c -> show c
    Vlist vs -> if vs /= [] then case head vs of
      Vchar _ -> "\"" ++ map (\(Vchar c) -> c) vs ++ "\""
      _ -> "[" ++ drop 2 (foldl (\s v -> s ++ ", " ++ printt v) "" vs) ++ "]"
      else "[]"
    Vsum e -> case e of Left x -> "left " ++ printt x
                        Right x -> "right " ++ printt x
    Vret v -> "opened " ++ printt v
    Vflag v -> "closed " ++ printt v
    Vmem v -> "mem " ++ show v
    Fix v -> "Fix " ++ printt v
    -- _ -> "NOT SUPPORTED: " ++ show v

-- ideally, we only need "return"
instance MyPrinter Comp where
  printt c = case c of
    Return v -> "return " ++ printt v -- TODO: when to add parentheses
    Op l v (y :. c) -> "op " ++ l ++ " " ++ printt v
      ++ " (" ++ y ++ " . " ++ printt c ++ ")"
    Sc l v (y :. c1) (z :. c2) -> "op " ++ l ++ " " ++ printt v
      ++ " (" ++ y ++ " . " ++ printt c1 ++ ")"
      ++ " (" ++ z ++ " . " ++ printt c2 ++ ")"
    Handle v c -> printt v ++ " # " ++ printt c
    Do x c1 c2 -> "do " ++ x ++ " <- " ++ printt c1 ++ "; " ++ printt c2
    App v1 v2 -> printt v1 ++ " " ++ printt v2
    Let x v c -> "let " ++ x ++ " = " ++ printt v ++ " in " ++ printt c
    LetRec x v c -> "letrec " ++ x ++ " = " ++ printt v ++ " in " ++ printt c
    App' _ -> error "App' is impossible"
    If v c1 c2 -> "if " ++ printt v ++ " then " ++ printt c1 ++ " else " ++ printt c2
    Case v x c1 y c2 -> "case " ++ printt v ++ " of "
      ++ "left " ++ x ++ " -> " ++ printt c1 ++ "\n"
      ++ "right " ++ y ++ " -> " ++ printt c2
    Eq v1 v2 -> printt v1 ++ " = " ++ printt v2
    Lt v1 v2 -> printt v1 ++ " > " ++ printt v2
    Add v1 v2 -> printt v1 ++ " + " ++ printt v2
    Mul v1 v2 -> printt v1 ++ " * " ++ printt v2
    Append v1 v2 -> printt v1 ++ " ++ " ++ printt v2
    AppendCut v1 v2 -> "append " ++ printt v1 ++ " " ++ printt v2
    -- ConcatMap v1 v2 -> "concatMap " ++ printt v1 ++ " " ++ printt v2
    Retrieve v1 v2 -> "retrieve " ++ printt v1 ++ " " ++ printt v2
    Update v1 v2 -> "update " ++ printt v1 ++ " " ++ printt v2
    Head v -> "head " ++ printt v
    Tail v -> "tail " ++ printt v
    Fst v -> "fst " ++ printt v
    Snd v -> "snd " ++ printt v
    Cons v vs -> "cons " ++ printt v ++ " " ++ printt vs
    Read v -> "read (" ++ printt v ++ ")"
    _ -> error $ "NOT SUPPORTED: " ++ show c


instance MyPrinter Handler where
  printt h = "{handler " ++ show (oplist h) ++ show (sclist h) ++ "}"

class MyTypePrinter a where
  printy :: a -> State (M.Map String String, [String]) String

instance MyTypePrinter VType where
  printy vt = case vt of
    TVar x _ -> do
      (m, alphabet) <- get
      case M.lookup x m of
        Just y -> return y
        Nothing -> do let (c:res) = alphabet
                      put (M.insert x c m, res)
                      return c
    TArr t1 t2 -> do
      s1 <- case t1 of
              TArr _ _ -> do s <- printy t1; return $ addParens s
              _ -> printy t1
      s2 <- printy t2
      return $ s1 ++ " -> " ++ s2
    TPair t1 t2 -> do
      s1 <- printy t1
      s2 <- printy t2
      return $ "(" ++ s1 ++ ", " ++ s2 ++ ")"
    TMem t1 t2 -> do
      s1 <- printy t1
      s2 <- printy t2
      return $ "Mem " ++ s1 ++ " " ++ s2
    TSum t1 t2 -> do
      s1 <- printy t1
      s2 <- printy t2
      return $ s1 ++ " + " ++ s2
    THand t1 t2 -> do
      s1 <- printy t1
      s2 <- printy t2
      return $ s1 ++ " => " ++ s2
    TList t -> do
      s <- printy t
      return $ "List " ++ s
    TCutList t -> do
      s <- printy t
      return $ "CutList " ++ s
    TUnit -> return "Unit"
    TChar -> return "Char"
    TBool -> return "Bool"
    TInt -> return "Int"
    TEmpty -> return "Empty"
    TApp m t -> printy (applyTyOpt m t)

instance MyTypePrinter EType where
  printy et = case et of
    EVar x _ -> do
      (m, alphabet) <- get
      case M.lookup x m of
        Just y -> return y
        Nothing -> do let (c:res) = alphabet
                      put (M.insert x c m, res)
                      return c
    EEmpty -> return "<>"
    ECons l t -> do
      let (ls, t') = getAllLabels (ECons l t)
      case t' of
        (EVar x _) -> do s <- printy t'; return $ "<" ++ printLabels ls ++ " | " ++ s ++ ">"
        EEmpty -> return $ "<" ++ printLabels ls ++ ">"
        _ -> error "impossible"
      -- s <- printy t
      -- return $ "<" ++ l ++ ";" ++ s ++ ">"

getAllLabels :: EType -> ([Name], EType)
getAllLabels (EVar x b) = ([], EVar x b)
getAllLabels EEmpty = ([], EEmpty)
getAllLabels (ECons l t) = let (res, et) = getAllLabels t
                           in (l : res, et)

printLabels :: [Name] -> String
printLabels [] = ""
printLabels [x] = x
printLabels (x:y:xs) = x ++ "; " ++ printLabels (y:xs)

instance MyTypePrinter CType where
  printy (CT vt et) = do
    s <- case vt of
          TArr _ _ -> do s <- printy vt; return $ addParens s
          TSum _ _ -> do s <- printy vt; return $ addParens s
          TApp m t -> case applyTyOpt m t of
                        TArr _ _ -> do s <- printy vt; return $ addParens s
                        TSum _ _ -> do s <- printy vt; return $ addParens s
                        _ -> printy vt
          _ -> printy vt
    es <- printy et
    return $ s ++ " ! " ++ es

instance MyTypePrinter SType where
  printy (Mono vt) = printy vt
  printy (Forall x k st) = do
    (m, alphabet) <- get
    sx <- case M.lookup x m of
            Just y -> return y
            Nothing -> do let (c:res) = alphabet
                          put (M.insert x c m, res)
                          return c
    s <- printy st
    return $ "∀" ++ sx ++ ":" ++ printt k ++ ". " ++ s

instance MyPrinter Kind where
  printt ValueType = "*"
  printt EffectType = "Eff"
  printt CompType = "I don't want to print a computation type :)"

instance (MyPrinter a, MyPrinter b) => MyPrinter (Either a b) where
  printt (Left x) = printt x
  printt (Right x) = printt x

instance (MyTypePrinter a, MyTypePrinter b) => MyTypePrinter (Either a b) where
  printy (Left x) = printy x
  printy (Right x) = printy x