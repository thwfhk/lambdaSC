{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use mapM_" #-}
{-# HLINT ignore "Use lambda-case" #-}
module Main where

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
import System.Environment
import qualified Data.Map as M

runParseValue :: String -> Except Err (Either ParseError Value)
runParseValue = runParserT parseValue emptyctx "CandyQwQ"

runParseComp :: String -> String -> Except Err (Either ParseError Comp)
runParseComp = runParserT parseComp emptyctx

runParseTyOpt :: String -> String -> Except Err (Either ParseError TypeOpt)
runParseTyOpt = runParserT parseTypeOpt emptyctx

runParseClauses :: String -> Except Err (Either ParseError [Clause])
runParseClauses = runParserT parseClauses emptyctx "CandyQwQ"

runParseCmds :: String -> String -> Except Err (Either ParseError [Command])
runParseCmds = runParserT parseCmds emptyctx

alphabets = map (:[]) ['a'..'z']

runFile :: IO ()
runFile = do
  args <- getArgs
  case args of
    [sourceFileName] -> do
      sourceFile <- readFile sourceFileName
      case runExcept (runParseCmds sourceFileName sourceFile) of
        Left err -> putStrLn $ "[PARSE FAILED 😵]: " ++ show err
        Right e -> case e of
          Left err -> putStrLn $ "[PARSE FAILED 😵]: " ++ show err
          Right cmds -> do
            putStrLn $ "[PARSE SUCCESS 🥳]:\n  " ++ show (length cmds)
              ++ " statements found"
            --  runStateT (runStateT (inferCmds cmds) []) 0
            let ((ts, _), _) = flip runState 0 . flip runStateT []
                             . runExceptT $ inferCmds cmds
            case ts of
              Left err -> putStrLn $ "[TYPE INFERENCE FAILED 😵]: " ++ show err
              Right ts -> do putStrLn "[TYPE INFERENCE SUCCESS 🥳]: "
                             let names = (\ x -> case x of Def s _ _ -> s
                                                           Run _ -> "") <$> cmds
                             mapM (\(n, t) -> putStrLn $ "  " ++
                                          (if n /= "" then n ++ " : " else "") ++
                                          evalState (printy t) (M.empty, alphabets)) $ zip names ts;
                             return ()
            let cs = cmds2comps cmds
            putStrLn "[EVALUATING PROCESS]:"
            -- mapM (\ c -> putStrLn $ show c ++ " ||| " ++ show (eval c)) cs
            mapM (\ c -> do
                putStrLn $ "      " ++ printt c
                let ds = evals c
                mapM (\ d -> putStrLn $ "  ~>  " ++ printt d) ds
                putStrLn $ "  🥳  " ++ removeReturn (printt (eval c))
              ) cs
            return ()
    _ -> putStrLn "file name error, enter REPL" >> repl

removeReturn :: String -> String
removeReturn s = if take 6 s == "return" then drop 7 s else s

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

test :: IO ()
test = do
  args <- getArgs
  case args of
    [sourceFileName, dstFileName] -> do
      sourceFile <- readFile sourceFileName
      putStrLn sourceFile
      case runExcept (runParseTyOpt sourceFileName sourceFile) of
        Left err -> print err
        Right e -> case e of
          Left err -> print err
          Right v -> print (show v)
    _ -> error "file error"
  putStrLn ""

main :: IO ()
main = runFile