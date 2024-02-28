{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Context where

import Syntax
import Data.List
import Text.Parsec (SourcePos)
import Data.Functor.Identity (Identity)
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as S


data Binding
  = NameBind
  | TypeBind SType
  deriving (Show, Eq)

type Context = [(Name, Binding)]

sigma :: [(Name, (VType, VType))]
sigma =
  [ ("choose", (TUnit, TBool))
  , ("fail", (TUnit, TEmpty))
  , ("once", (TUnit, TUnit))
  , ("twice", (TUnit, TUnit))
  , ("raise", (tString, TEmpty))
  , ("catch", (tString, TBool))
  , ("inc", (TUnit, TInt))
  , ("get", (tString, TInt))
  , ("ask", (TUnit, TInt))
  , ("foo", (TUnit, TInt))
  , ("lread", (TArr TInt (CT TInt (EVar "mu" True)), TUnit))
    -- lambda_sc does not support real polymorphic operations
    -- I hack here by restricting the variable name to be mu
  , ("put", (TPair tString TInt, TUnit))
  , ("local", (TPair tString TInt, TUnit))
  , ("cut", (TUnit, TUnit))
  , ("call", (TUnit, TUnit))
  , ("depth", (TInt, TUnit))
  , ("token", (TChar, TChar))
  ]

isOp :: Name -> Bool
isOp "token"  = True
isOp "depth"  = False
isOp "call"   = False
isOp "cut"    = True
isOp "local"  = False
isOp "put"    = True
isOp "get"    = True
isOp "inc"    = True
isOp "catch"  = False
isOp "raise"  = True
isOp "once"   = False
isOp "twice"   = False
isOp "fail"   = True
isOp "choose" = True
isOp "ask"    = True
isOp "foo"    = True
isOp "lread"  = False
isOp _ = undefined

isSc :: Name -> Bool
isSc = not . isOp

emptyctx :: Context
emptyctx = []

onlyTypes :: Context -> [SType]
onlyTypes [] = []
onlyTypes ((_, NameBind) : ctx) = onlyTypes ctx
onlyTypes ((_, TypeBind t) : ctx) = t : onlyTypes ctx

addBinding :: [(Name, b)] -> (Name, b) -> [(Name, b)]
addBinding ctx (x, bind) = (x, bind) : ctx

addBindings :: [(Name, b)] -> [(Name, b)] -> [(Name, b)]
addBindings = foldl addBinding -- reverse order

-- used in parseVar
name2index :: Context -> Name -> SourcePos -> Either Err Int
name2index ctx name pos =
  case findIndex ((== name). fst) ctx of
    Just ind -> Right ind
    Nothing -> Left $ "Unbounded variable " ++ name ++ " at " ++ show pos

name2entry :: Monad m => [(Name, b)] -> Name -> ExceptT Err m (Name, b)
name2entry ctx name =
  case find ((== name). fst) ctx of
    Just x -> return x
    Nothing -> throwError $ "name \"" ++ name ++ "\" not found"

-- not used yet
-- index2entry :: Monad m => [(Name, b)] -> Int -> ExceptT Err m (Name, b)
-- index2entry ctx x
--   | length ctx > x = return $ ctx !! x
--   | otherwise = throwError $ "index " ++ show x
--               ++ " overflow (context length " ++ show (length ctx) ++ ")"


index2type :: Monad m => Context -> Int -> ExceptT Err m SType
index2type ctx x
  | length ctx > x = case snd $ ctx !! x of
                          NameBind -> throwError "invalid binding type"
                          TypeBind t -> return t
  | otherwise = throwError $ "index " ++ show x
              ++ " overflow (context length " ++ show (length ctx) ++ ")"


instance FreeVars Context where
  freeVars [] = S.empty
  freeVars ((x, NameBind) : xs) = freeVars xs
  freeVars ((x, TypeBind t) : xs) = freeVars t `S.union` freeVars xs