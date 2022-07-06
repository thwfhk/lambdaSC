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
                  Right ts -> let names = (\ x -> case x of Def s _ _ -> s
                                                            Run _ -> "") <$> cmds
                              in let res = concatMap (\(n, t) -> "  " ++
                                           (if n /= "" then n ++ " : " else "") ++
                                           evalState (printy t) (M.empty, alphabets) ++"\n") $ zip names ts;
                              in "[TYPE INFERENCE SUCCESS 🥳]:\n" ++ string2html res
        in let cs = cmds2comps cmds
          --  putStrLn (show cs)
        in let info2 = "[EVALUATION RESULTS 🥳]:"
        in let results = concatMap (\ c -> " " ++ removeReturn (printt (eval c)) ++ "\n") cs
        in info ++ "\n" ++ tres ++ "\n" ++ info2 ++ "\n" ++ results

removeReturn :: String -> String
removeReturn s = if take 6 s == "return" then drop 7 s else s

string2html :: String -> String
string2html s = concatMap f s
  where
    f '<' = "&lt;"
    f '>' = "&gt;"
    f x   = x : []