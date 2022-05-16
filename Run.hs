module Run where

import Syntax
import Context
import Parser
import Evaluation
import PrettyPrinter
import Text.Parsec
import Control.Monad.Except

runParseCmds :: String -> String -> Except Err (Either ParseError [Command])
runParseCmds = runParserT parseCmds emptyctx

interpret :: String -> String
interpret input = 
  case runExcept (runParseCmds "input" input) of
    Left err -> "[PARSE FAILED 😵]: " ++ show err
    Right e -> case e of
      Left err -> "[PARSE FAILED 😵]: " ++ show err
      Right cmds -> let info = "[PARSE SUCCESS 🥳]:\n  " ++ show (length cmds)
                         ++ " statements found"
                    in let cs = cmds2comps cmds
                      --  putStrLn (show cs)
                    in let info2 = "[EVALUATION RESULTS]:"
                    in let results = concatMap (\ c -> "  " ++ printComp (eval c) ++ "\n") cs
                    in info ++ "\n" ++ info2 ++ "\n" ++ results