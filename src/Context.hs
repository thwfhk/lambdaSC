{-# LANGUAGE FlexibleContexts #-}

module Context where

import Syntax
import Data.List
import Text.Parsec (ParsecT, getState, setState)
import Data.Functor.Identity (Identity)
import Control.Monad.State
import Control.Monad.Except


data Binding = NameBind deriving (Show, Eq)

type Context = [(Name, Binding)]

emptyctx :: Context
emptyctx = []

addBinding :: [(Name, b)] -> (Name, b) -> [(Name, b)]
addBinding ctx (x, bind) = (x, bind) : ctx

addBindings :: [(Name, b)] -> [(Name, b)] -> [(Name, b)]
addBindings ctx [] = ctx
addBindings ctx (x:xs) = addBindings (addBinding ctx x) xs -- reverse order

name2index :: Context -> Name -> Either Err Int
name2index ctx name =
  case findIndex ((== name). fst) ctx of
    Just ind -> Right ind
    Nothing -> Left $ "Unbounded variable \"" ++ name ++ "\""

name2entry :: [(Name, b)] -> Name -> Either Err (Name, b)
name2entry ctx name =
  case find ((== name). fst) ctx of
    Just x -> Right x
    Nothing -> Left $ "Unbounded variable \"" ++ name ++ "\""

index2entry :: [(Name, b)] -> Int -> Either Err (Name, b)
index2entry ctx x
  | length ctx > x = Right $ ctx !! x
  | otherwise = Left $ "index " ++ show x
              ++ " overflow (context length " ++ show (length ctx) ++ ")"