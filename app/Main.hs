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

inferCmd :: Command -> W (Either SType CType, Theta)
inferCmd (Def x v False) = do
  (a, theta) <- inferV v
  sigma <- gen theta a
  return (Left sigma, theta)
inferCmd (Def x v True) = do
  alpha <- freshV
  ctx <- get
  put $ addBinding ctx (x, TypeBind $ Mono alpha)
  (a, theta1) <- inferV v
  theta2 <- unify (theta1 <@> alpha) a
  sigma <- gen (theta2 <^> theta1) (theta2 <@> a)
  put ctx
  return (Left sigma, theta2 <^> theta1)
inferCmd (Run c) = do
  (a, theta) <- inferC c
  return (Right a, theta)

inferCmds :: [Command] -> W [Either SType CType]
inferCmds [] = return []
inferCmds (Def x v b : cs) = do
  (t, theta) <- inferCmd (Def x v b)
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

isDef (Def _ _ _) = True
isDef _ = False

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
            putStrLn "[EVALUATION RESULTS 🥳]:"
            --  mapM (\ c -> putStrLn $ "  " ++ show (eval c)) cs
            mapM (\ c -> putStrLn $ " " ++ dropWhile (/= ' ') (printt (eval c))) cs
            return ()
    _ -> putStrLn "file name error, enter REPL" >> repl

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