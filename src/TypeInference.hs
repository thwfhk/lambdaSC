module TypeInference where

import Syntax
import Context
import Substitution
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Set as S

type W = ExceptT Err (StateT Context (State Int))

freshV :: W VType
freshV = do
  i <- lift . lift $ get
  lift . lift $ put (i+1)
  return (TVar ('$' : show i))

freshE :: W EType
freshE = do
  i <- lift . lift $ get
  lift . lift $ put (i+1)
  return (EVar ('$' : show i))

inst :: SType -> W VType
inst (Mono t) = return t
inst (Forall x k t) = case k of
  ValueType -> do
    i <- freshV
    t' <- inst t
    return (apply (M.singleton x (Left i)) t')
  EffectType -> do
    i <- freshE
    t' <- inst t
    return (apply (M.singleton x (Right i)) t')
  CompType -> throwError "computation type should not be bound"

gen :: Theta -> VType -> W SType
gen theta t = do
  ctx <- get
  let cs = S.unions . map freeVars . onlyTypes $ ctx
  let vs = freeVars t `S.difference` cs
  return (S.foldr (uncurry Forall) (Mono t) vs)


unify :: (VType, VType) -> W Theta
unify = undefined


inferV :: Value -> W (VType, Theta)
inferV (Var x n) = do
  ctx <- get
  tau <- index2type ctx n
  sigma <- inst tau
  return (sigma, M.empty)
inferV (Lam x c) = do
  alpha <- freshV
  ctx <- get
  let nctx = addBinding ctx (x, TypeBind (Mono alpha))
  put nctx
  (uC, theta) <- inferC c
  put ctx
  return (TArr (apply theta alpha) uC, theta)
inferV _ = undefined


inferC :: Comp -> W (CType, Theta)
inferC (App v1 v2) = do
  (a1, theta1) <- inferV v1
  (a2, theta2) <- inferV v2
  alpha <- freshV
  mu <- freshE
  theta3 <- unify (apply theta2 a1, TArr a2 (CT alpha mu))
  return (apply theta3 (CT alpha mu), theta3 <^> theta2 <^> theta1)
inferC (Let x v c) = do
  (a1, theta1) <- inferV v
  sigma <- gen theta1 a1
  ctx <- get
  let nctx = addBinding (map (apply2bind theta1) ctx) (x, TypeBind sigma)
  put nctx
  (uC, theta2) <- inferC c
  put ctx
  return (uC, theta2 <^> theta1)
inferC _ = undefined

apply2bind :: Theta -> (a, Binding) -> (a, Binding)
apply2bind s (x, b) = case b of
  TypeBind t -> (x, TypeBind (apply s t))
  NameBind -> error "TypeBind expected"
-- test :: StateT Int (State Bool) (Int, Bool)
-- test = do
--   put 1
--   x <- get
--   lift $ put True
--   y <- lift get
--   return (x, y)

-- test2 = flip runState True $ runStateT test 0

-- -- >>> test2
-- -- (((1,True),1),True)
