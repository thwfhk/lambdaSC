module PrettyPrinter where

import Syntax

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
    Vstr s -> s
    Vlist vs -> "[" ++ drop 2 (foldl (\s v -> s ++ ", " ++ printt v) "" vs) ++ "]"
    Vsum e -> case e of Left x -> "left " ++ printt x
                        Right x -> "right " ++ printt x
    Vret v -> "opened " ++ printt v
    Vflag v -> "closed " ++ printt v
    Vmem v -> "mem " ++ show v
  -- _ -> undefined 

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
    App' _ -> error "App' is impossible"
    If v c1 c2 -> "if " ++ printt v ++ " then " ++ printt c1 ++ " else " ++ printt c2
    Case v x c1 y c2 -> "case " ++ printt v ++ " of "
      ++ "left " ++ x ++ " -> " ++ printt c1 ++ "\n"
      ++ "right " ++ y ++ " -> " ++ printt c2
    Eq v1 v2 -> printt v1 ++ " = " ++ printt v2
    Lt v1 v2 -> printt v1 ++ " > " ++ printt v2
    Add v1 v2 -> printt v1 ++ " + " ++ printt v2
    Append v1 v2 -> printt v1 ++ " ++ " ++ printt v2
    ConcatMap v1 v2 -> "concatMap " ++ printt v1 ++ " " ++ printt v2
    Retrieve v1 v2 -> "retrieve " ++ printt v1 ++ " " ++ printt v2
    Update v1 v2 -> "update " ++ printt v1 ++ " " ++ printt v2
    Head v -> "head " ++ printt v
    Fst v -> "fst " ++ printt v
    Snd v -> "snd " ++ printt v
    _ -> undefined 
  

instance MyPrinter Handler where
  printt h = "I don't want to print a handler :)"

instance MyPrinter VType where
  printt vt = case vt of
    TVar x -> x
    TArr t1 t2 -> addParens (printt t1) ++ " -> " ++ addParens (printt t2)
    TPair t1 t2 -> "(" ++ printt t1 ++ ", " ++ printt t2 ++ ")"
    TMem t1 t2 -> "Mem " ++ printt t1 ++ " " ++ printt t2
    TSum t1 t2 -> printt t1 ++ " + " ++ printt t2
    THand t1 t2 -> printt t1 ++ " => " ++ printt t2
    TList t -> "List " ++ printt t
    TCutList t -> "CutList " ++ printt t
    TUnit -> "Unit"
    TString -> "String"
    TBool -> "Bool"
    TInt -> "Int"
    TEmpty -> "Empty"

instance MyPrinter EType where
  printt et = case et of
    EVar x -> x
    EEmpty -> "<>"
    ECons l t -> "<" ++ l ++ ";" ++ printt t ++ ">"

instance MyPrinter CType where
  printt (CT vt et) = printt vt ++ " ! " ++ printt et

instance MyPrinter SType where
  printt (Mono vt) = printt vt
  printt (Forall x k st) = "∀ " ++ x ++ " : " ++ printt k ++ " . " ++ printt st

instance MyPrinter Kind where
  printt ValueType = "*"
  printt EffectType = "Eff"
  printt CompType = "I don't want to print a computation type :)"

instance (MyPrinter a, MyPrinter b) => MyPrinter (Either a b) where
  printt (Left x) = printt x
  printt (Right x) = printt x