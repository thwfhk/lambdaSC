{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use mapM_" #-}
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
          Right cmds -> do
            putStrLn $ "[PARSE SUCCESS 🥳]:\n  " ++ show (length cmds)
              ++ " statements found"
            --  runStateT (runStateT (inferCmds cmds) []) 0
            let ((ts, _), _) = flip runState 0 . flip runStateT []
                             . runExceptT $ inferCmds cmds
            case ts of
              Left err -> putStrLn $ "[TYPE INFERENCE FAILED 😵]: " ++ show err
              Right ts -> do putStrLn "[TYPE INFERENCE SUCCESS 🥳]: "
                             mapM (\t -> putStrLn $ "  " ++ printt t) ts;
                             return ()
            let cs = cmds2comps cmds
            --  putStrLn (show cs)
            putStrLn "[EVALUATION RESULTS 🥳]:"
            --  mapM (\ c -> putStrLn $ "  " ++ show (eval c)) cs
            mapM (\ c -> putStrLn $ "  " ++ printt (eval c)) cs
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