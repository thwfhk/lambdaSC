module PrettyPrinter where

import Syntax

-- ideally, we only need printValue to show the results
printValue :: Value -> String
printValue v = case v of
  Var x _ -> x
  Lam x c -> "\\ " ++ x ++ " . " ++ printComp c
  Vunit   -> "unit"
  Vpair (v1, v2) -> "(" ++ printValue v1 ++ ", " ++ printValue v2 ++ ")"
  Vhandler h -> printHandler h
  Vbool b -> if b then "true" else "false"
  Vint n -> show n
  Vchar c -> show c
  Vstr s -> s
  Vlist vs -> "[" ++ drop 2 (foldl (\s v -> s ++ ", " ++ printValue v) "" vs) ++ "]"
  Vsum e -> case e of Left x -> "left " ++ printValue x
                      Right x -> "right " ++ printValue x
  Vret v -> "ret " ++ printValue v
  Vflag v -> "flag " ++ printValue v
  Vmem v -> "mem " ++ show v
  -- _ -> undefined 

-- ideally, we only need "return"
printComp :: Comp -> String
printComp c = case c of
  Return v -> "return " ++ printValue v
  Op l v (y :. c) -> "op " ++ l ++ " " ++ printValue v
    ++ " (" ++ y ++ " . " ++ printComp c ++ ")"
  Sc l v (y :. c1) (z :. c2) -> "op " ++ l ++ " " ++ printValue v
    ++ " (" ++ y ++ " . " ++ printComp c1 ++ ")"
    ++ " (" ++ z ++ " . " ++ printComp c2 ++ ")"
  Handle v c -> printValue v ++ " # " ++ printComp c
  Do x c1 c2 -> "do " ++ x ++ " <- " ++ printComp c1 ++ "; " ++ printComp c2
  App v1 v2 -> printValue v1 ++ " " ++ printValue v2
  Let x v c -> "let " ++ x ++ " = " ++ printValue v ++ " in " ++ printComp c
  App' _ -> error "App' is impossible"
  If v c1 c2 -> "if " ++ printValue v ++ " then " ++ printComp c1 ++ " else " ++ printComp c2
  Case v x c1 y c2 -> "case " ++ printValue v ++ " of "
    ++ "left " ++ x ++ " -> " ++ printComp c1 ++ "\n"
    ++ "right " ++ y ++ " -> " ++ printComp c2
  Eq v1 v2 -> printValue v1 ++ " = " ++ printValue v2
  Lt v1 v2 -> printValue v1 ++ " > " ++ printValue v2
  Add v1 v2 -> printValue v1 ++ " + " ++ printValue v2
  Append v1 v2 -> printValue v1 ++ " ++ " ++ printValue v2
  ConcatMap v1 v2 -> "concatMap " ++ printValue v1 ++ " " ++ printValue v2
  Retrieve v1 v2 -> "retrieve " ++ printValue v1 ++ " " ++ printValue v2
  Update v1 v2 -> "update " ++ printValue v1 ++ " " ++ printValue v2
  Head v -> "head " ++ printValue v
  Fst v -> "fst " ++ printValue v
  Snd v -> "snd " ++ printValue v
  _ -> undefined 


printHandler :: Handler -> String
printHandler h = "I don't want to print a handler :)"