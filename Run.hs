module Run where

import Syntax
import Context
import Parser
import Evaluation
import TypeInference
import Substitution
import PrettyPrinter
import Text.Parsec
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M

runParseCmds :: String -> String -> Except Err (Either ParseError [Command])
runParseCmds = runParserT parseCmds emptyctx

inferCmd :: Command -> W (Either SType CType, Theta)
inferCmd (Def x v) = do
  (a, theta) <- inferV v
  sigma <- gen theta a
  return (Left sigma, theta)
inferCmd (Run c) = do
  (a, theta) <- inferC c
  return (Right a, theta)

inferCmds :: [Command] -> W [Either SType CType]
inferCmds [] = return []
inferCmds (Def x v : cs) = do
  (t, theta) <- inferCmd (Def x v)
  case t of
    Left sigma -> do
      ctx <- get
      let nctx = addBinding (map (apply2bind theta) ctx) (x, TypeBind sigma)
      put nctx
    Right _ -> throwError "[IMPOSSIBLE] expect a type scheme"
  ts <- inferCmds cs
  return $ t : ts
inferCmds (Run c : cs) = do
  (t, _) <- inferCmd (Run c)
  ts <- inferCmds cs
  return $ t : ts

alphabets = map (:[]) ['a'..'z']

interpret :: String -> String
interpret input = 
  case runExcept (runParseCmds "input" input) of
    Left err -> "[PARSE FAILED 😵]: " ++ show err
    Right e -> case e of
      Left err -> "[PARSE FAILED 😵]: " ++ show err
      Right cmds -> 
        let info = "[PARSE SUCCESS 🥳]:\n  " ++ show (length cmds)
             ++ " statements found\n"
        in let ((ts, _), _) = flip runState 0 . flip runStateT []
                 . runExceptT $ inferCmds cmds
        in let tres =
                case ts of
                  Left err -> "[TYPE INFERENCE FAILED 😵]: " ++ show err
                  Right ts -> let names = (\ x -> case x of Def s _ -> s
                                                            Run _ -> "") <$> cmds
                              in let res = concatMap (\(n, t) -> "  " ++
                                           (if n /= "" then n ++ " : " else "") ++
                                           evalState (printy t) (M.empty, alphabets) ++"\n") $ zip names ts;
                              in "[TYPE INFERENCE SUCCESS 🥳]:\n" ++ string2html res
        in let cs = cmds2comps cmds
          --  putStrLn (show cs)
        in let info2 = "[EVALUATION RESULTS 🥳]:"
        in let results = concatMap (\ c -> " " ++ dropWhile (/= ' ') (printt (eval c)) ++ "\n") cs
        in info ++ "\n" ++ tres ++ "\n" ++ info2 ++ "\n" ++ results


string2html :: String -> String
string2html s = concatMap f s
  where
    f '<' = "&lt;"
    f '>' = "&gt;"
    f x   = x : []