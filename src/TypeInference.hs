module TypeInference where

import Syntax
import Context
import Substitution
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace

type W = ExceptT Err (StateT Context (State Int))

----------------------------------------------------------------
-- utilities

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


----------------------------------------------------------------
-- unification


class Unifiable a where
  unify :: a -> a -> W Theta

instance Unifiable VType where
  unify (TVar x) (TVar y) | x == y = return M.empty
  unify (TVar x) t | x `S.member` S.map fst (freeVars t) = throwError
    "[unification fail] free value type variable appearing in the other type"
  unify (TVar x) t  = return $ M.singleton x (Left t)
  unify t (TVar x) = unify (TVar x) t
  unify (TArr t1 c1) (TArr t2 c2) = do
    theta1 <- unify t1 t2
    theta2 <- unify (apply theta1 c1) (apply theta1 c2) -- NOTE: need to apply theta1
    return $ theta2 <^> theta1
  unify (TPair t1 t2) (TPair t1' t2') = do
    theta1 <- unify t1 t1'
    theta2 <- unify (apply theta1 t2) (apply theta1 t2')
    return $ theta2 <^> theta1
  unify _ _ = undefined

instance Unifiable CType where
  unify (CT t1 e1) (CT t2 e2) = do
    theta1 <- unify t1 t2
    theta2 <- unify (apply theta1 e1) (apply theta1 e2)
    return $ theta2 <^> theta1

-- NOTE: simplification: there is no need to substitute labels
instance Unifiable EType where
  unify EEmpty EEmpty = return M.empty
  unify EEmpty _ = throwError
    "[unification fail] unify an empty row with a non-empty row"
  -- repetition of TVar rules
  unify (EVar x) (EVar y) | x == y = return M.empty
  unify (EVar x) t | x `S.member` S.map fst (freeVars t) = throwError
    "[unification fail] free effect type variable appearing in the other type"
  unify (EVar x) t  = return $ M.singleton x (Right t)
  unify t (EVar x) = unify (EVar x) t
  -- t2 must also be a ECons
  unify (ECons l t1) t2 = do
    t3 <- findLabel l t2
    unify t1 t3

findLabel :: Name -> EType -> W EType
findLabel x EEmpty = throwError $ "findLabel: no label " ++ x ++ " found"
findLabel x (EVar y) = throwError $ "findLabel: no label " ++ x ++ " found"
findLabel x (ECons l t) = if l == x then return t
                          else do t' <- findLabel x t; return $ ECons l t'

----------------------------------------------------------------

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
inferV Vunit = return (TUnit, M.empty)
inferV (Vbool _) = return (TBool, M.empty)
inferV (Vint _) = return (TInt, M.empty)
inferV (Vpair (v1, v2)) = do
  (a1, theta1) <- inferV v1
  ctx <- get
  let nctx = map (apply2bind theta1) ctx
  put nctx
  (a2, theta2) <- inferV v2
  put ctx
  return (TPair (apply theta1 a1) a2, theta2 <^> theta1)

inferV _ = undefined


inferC :: Comp -> W (CType, Theta)
inferC (App v1 v2) = do
  (a1, theta1) <- inferV v1
  ctx <- get
  let nctx = map (apply2bind theta1) ctx
  put nctx
  (a2, theta2) <- inferV v2
  alpha <- freshV
  mu <- freshE
  theta3 <- unify (apply theta2 a1) (TArr a2 (CT alpha mu))
  -- traceM $ "trace: " ++ show (apply theta2 a1) ++ " ||| " ++ show (TArr a2 (CT alpha mu))
  -- traceM $ show (M.lookup "$4" theta3) ++ " ||| " ++ show (M.lookup "$2" theta3)
  put ctx
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
inferC (Return v) = do
  (a, theta) <- inferV v
  mu <- freshE
  return (CT a mu, theta)
inferC (Fst v) = do
  (a, theta1) <- inferV v
  alpha1 <- freshV
  alpha2 <- freshV
  theta2 <- unify a (TPair alpha1 alpha2)
  mu <- freshE
  return (CT (apply theta2 alpha1) mu, theta2 <^> theta1)
inferC oth = trace (show oth) undefined

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
