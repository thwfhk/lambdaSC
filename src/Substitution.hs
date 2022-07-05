{-# LANGUAGE FlexibleInstances #-}

module Substitution where

import Syntax
import Context
import qualified Data.Map as M

-- | Map variable names to value types or effect types
type Theta = M.Map Name Type

-- apply a substitution to some type
class Applicable a where
  apply :: Theta -> a -> a

instance Applicable VType where
  apply s (TVar x b) = case M.lookup x s of
    Nothing -> TVar x b
    Just (Left t) -> apply s t
    _ -> error "expect a value type variable"
  apply s (TArr t1 t2) = TArr (apply s t1) (apply s t2)
  apply s (TPair t1 t2) = TPair (apply s t1) (apply s t2)
  apply s (TMem t1 t2) = TMem (apply s t1) (apply s t2)
  apply s (TSum t1 t2) = TSum (apply s t1) (apply s t2)
  apply s (THand t1 t2) = THand (apply s t1) (apply s t2)
  apply s (TList t) = TList (apply s t)
  apply s (TCutList t) = TCutList (apply s t)
  apply s TChar = TChar
  apply s TUnit = TUnit
  apply s TBool = TBool
  apply s TInt = TInt
  apply s TEmpty = TEmpty
  apply s (TApp m a) = TApp (apply s m) (apply s a)

instance Applicable CType where
  apply s (CT v e) = CT (apply s v) (apply s e)

instance Applicable EType where
  apply s (EVar x b) = case M.lookup x s of
    Nothing -> EVar x b
    Just (Right t) -> apply s t
    _ -> error "expect an effect type variable"
  apply s EEmpty = EEmpty
  apply s (ECons x t) = ECons x (apply s t)

instance Applicable SType where
  apply s (Mono t) = Mono (apply s t)
  apply s (Forall x k t) = Forall x k (apply (M.delete x s) t)
            -- g (MonoT t) = monoT (apply s t)
            -- g (ForAllT x t) = forAllT x (apply (M.delete x s) t)

instance Applicable Type where
  apply s (Left t) = Left $ apply s t
  apply s (Right t) = Right $ apply s t

instance Applicable TypeOpt where
  apply s (TNil t) = TNil (apply s t)
  apply s (TAbs x k t) = TAbs x k (apply (M.delete x s) t)

infixr 7 <@> 
(<@>) :: Applicable a => Theta -> a -> a
(<@>) = apply

infixr <^>
(<^>) :: Theta -> Theta -> Theta
s1 <^> s2 = M.map (apply s1) s2 `M.union` s1


apply2bind :: Theta -> (a, Binding) -> (a, Binding)
apply2bind s (x, b) = case b of
  TypeBind t -> (x, TypeBind (apply s t))
  NameBind -> error "[IMPOSSIBLE] TypeBind expected"

instance Applicable Context where
  apply s ctx = map (apply2bind s) ctx