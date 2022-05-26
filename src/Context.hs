{-# LANGUAGE FlexibleContexts #-}

module Context where

import Syntax
import Data.List
import Text.Parsec (SourcePos)
import Data.Functor.Identity (Identity)
import Control.Monad.State
import Control.Monad.Except


data Binding
  = NameBind
  | TypeBind SType
  deriving (Show, Eq)

type Context = [(Name, Binding)]

sigma :: [(Name, (VType, VType))]
sigma = [("or", (TUnit, TBool)), ("fail", (TUnit, TEmpty))]

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

-- not used yet
name2entry :: [(Name, b)] -> Name -> Either Err (Name, b)
name2entry ctx name =
  case find ((== name). fst) ctx of
    Just x -> Right x
    Nothing -> Left $ "Unbounded variable \"" ++ name ++ "\""

index2entry :: Monad m => [(Name, b)] -> Int -> ExceptT Err m (Name, b)
index2entry ctx x
  | length ctx > x = return $ ctx !! x
  | otherwise = throwError $ "index " ++ show x
              ++ " overflow (context length " ++ show (length ctx) ++ ")"


index2type :: Monad m => Context -> Int -> ExceptT Err m SType
index2type ctx x
  | length ctx > x = case snd $ ctx !! x of
                          NameBind -> throwError "invalid binding type"
                          TypeBind t -> return t
  | otherwise = throwError $ "index " ++ show x
              ++ " overflow (context length " ++ show (length ctx) ++ ")"