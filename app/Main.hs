module Main where

import Syntax
import Context
import Parser
import Evaluation
import Text.Parsec
import Control.Monad.Except
import System.Environment

runParseValue :: String -> Except Err (Either ParseError Value)
runParseValue = runParserT parseValue emptyctx "CandyQwQ"

runParseComp :: String -> String -> Except Err (Either ParseError Comp)
runParseComp = runParserT parseComp emptyctx

runParseClauses :: String -> Except Err (Either ParseError [Clause])
runParseClauses = runParserT parseClauses emptyctx "CandyQwQ"

fromFile :: IO ()
fromFile = do
  args <- getArgs
  case args of
    [sourceFileName, dstFileName] -> do
      sourceFile <- readFile sourceFileName
      case runExcept (runParseComp sourceFileName sourceFile) of
        Left err -> putStrLn $ "[PARSE FAILED 😵]: " ++ show err
        Right e -> case e of
          Left err -> putStrLn $ "[PARSE FAILED 😵]: " ++ show err
          Right c -> do putStrLn $ "[PARSE SUCCESS 🥳]:\n  " ++ show c
                        putStrLn $ "[EVALUATION RESULT]:\n  " ++ show (eval c)
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
main = fromFile