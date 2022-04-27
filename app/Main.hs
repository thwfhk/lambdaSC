module Main where

import Syntax
import Context
import Parser
import Evaluation
import PrettyPrinter
import Text.Parsec
import Control.Monad.Except
import System.Environment

runParseValue :: String -> Except Err (Either ParseError Value)
runParseValue = runParserT parseValue emptyctx "CandyQwQ"

runParseComp :: String -> String -> Except Err (Either ParseError Comp)
runParseComp = runParserT parseComp emptyctx

runParseClauses :: String -> Except Err (Either ParseError [Clause])
runParseClauses = runParserT parseClauses emptyctx "CandyQwQ"

runParseCmds :: String -> String -> Except Err (Either ParseError [Command])
runParseCmds = runParserT parseCmds emptyctx

runFile :: IO ()
runFile = do
  args <- getArgs
  case args of
    [sourceFileName, dstFileName] -> do
      sourceFile <- readFile sourceFileName
      case runExcept (runParseCmds sourceFileName sourceFile) of
        Left err -> putStrLn $ "[PARSE FAILED 😵]: " ++ show err
        Right e -> case e of
          Left err -> putStrLn $ "[PARSE FAILED 😵]: " ++ show err
          Right cmds -> do putStrLn $ "[PARSE SUCCESS 🥳]:\n  " ++ show (length cmds)
                             ++ " statements found"
                           let cs = cmds2comps cmds
                          --  putStrLn (show cs)
                           putStrLn $ "[EVALUATION RESULTS 🥳]:"
                          --  mapM (\ c -> putStrLn $ "  " ++ show (eval c)) cs
                           mapM (\ c -> putStrLn $ "  " ++ printComp (eval c)) cs
                           return ()
    _ -> putStrLn "file names error, enter REPL" >> repl

repl :: IO ()
repl = do
  prog <- getLine
  case runExcept (runParseValue prog) of
    Left err -> print err
    Right e -> case e of
      Left err -> print err
      Right v -> print (show v)
  putStrLn ""
  repl

main :: IO ()
main = runFile