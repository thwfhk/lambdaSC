{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use bimap" #-}
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
  unify (THand t1 t2) (THand t1' t2') = do
    theta1 <- unify t1 t1'
    theta2 <- unify (apply theta1 t2) (apply theta1 t2')
    return $ theta2 <^> theta1
  unify (TList t) (TList t') = do
    unify t t'
  unify t1 t2 | t1 == t2 = return M.empty
  unify t1 t2 = error $ "unify undefined for " ++ show t1 ++ " and "  ++ show t2
  -- unify _ _ = undefined

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

unifyList :: (Unifiable a, Applicable a) => [(a, a)] -> W Theta
unifyList [] = return M.empty
unifyList ((t1, t2) : cs) = do
  theta <- unify t1 t2
  let cs' = map (\ (t1, t2) -> (theta <@> t1, theta <@> t2)) cs
  theta' <- unifyList cs'
  return (theta' <^> theta)
  -- theta' <- un
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
  let nctx = addBinding ctx (x, TypeBind $ Mono alpha)
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
  let nctx = apply theta1 ctx
  put nctx
  (a2, theta2) <- inferV v2
  put ctx
  return (TPair (apply theta1 a1) a2, theta2 <^> theta1)
inferV (Vlist []) = do
  alpha <- freshV
  return (TList alpha, M.empty)
inferV (Vlist (v:vs)) = do
  (a1, theta1) <- inferV v
  ctx <- get
  put (theta1 <@> ctx)
  (a2, theta2) <- inferV (Vlist vs)
  put ctx
  theta3 <- unify (TList (theta2 <@> a1)) a2
  return (theta3 <@> a2, theta3 <^> theta2 <^> theta1)

inferV (Vhandler h) = do
  alpha <- freshV
  mu <- freshE
  let f = appendEff (oplist h ++ sclist h) mu
  ctx <- get
  -- return clause
  let (x, cr) = hreturn h
  let nctx = addBinding ctx (x, TypeBind $ Mono alpha)
  put nctx
  (uC, theta1) <- inferC cr
  -- op & sc clauses
  let nctx = theta1 <@> ctx
  put nctx
  (uC', theta2) <- inferOpr h
  -- fwd clauses
  let nctx = theta2 <@> theta1 <@> ctx 
  put nctx
  -- (uC'', theta3) <- inferFwd h
  let theta3 = M.empty -- TODO: add inferFwd
  put ctx
  let m = carrier h
  -- traceM $ "carrier: " ++ show m ++ " ; result: " ++ show (applyTyOpt m alpha)
  let uD = theta3 <@> theta2 <@> theta1 <@> CT (applyTyOpt m alpha) mu
  theta4 <- unifyList [(theta3 <@> theta2 <@> uC, uD), (theta3 <@> uC', uD)] -- , (uC'', uD)]
  let theta = theta4 <^> theta3 <^> theta2 <^> theta1
  return (theta <@> THand (CT alpha f) (CT (applyTyOpt m alpha) mu), theta)

inferV _ = undefined

inferOpr :: Handler -> W (CType, Theta)
inferOpr h = do
  (uC1, theta1) <- inferOp ops
  ctx <- get
  put (theta1 <@> ctx)
  (uC2, theta2) <- inferSc scs
  put ctx
  theta3 <- unify (theta2 <@> uC1) uC2
  return (theta3 <@> uC2, theta3 <^> theta2 <^> theta1)
  where
    ops = map fop (oplist h)
    scs = map fsc (sclist h)
    fop l = case hop h l of
      Just t -> (l, t)
      Nothing -> error "impossible"
    fsc l = case hsc h l of
      Just t -> (l, t)
      Nothing -> error "impossible"

-- (l, (x, k, c))
inferOp :: [(Name, (Name, Name, Comp))] -> W (CType, Theta)
inferOp [] = do
  alpha <- freshV
  mu <- freshE
  return (CT alpha mu, M.empty)
inferOp ((l, (x, k, c)) : ops) = do
  (_, (al, bl)) <- name2entry sigma l
  alpha <- freshV
  mu <- freshE
  (uD, theta1) <- inferOp ops
  ctx <- get
  let nctx = addBindings (theta1 <@> ctx) [ (x, TypeBind $ Mono al)
                                          , (k, TypeBind . Mono $ TArr bl (CT alpha mu))]
  put nctx
  (uC, theta2) <- inferC c
  put ctx
  theta3 <- unifyList [(theta2 <@> CT alpha mu, uC), (theta2 <@> CT alpha mu, theta2 <@> uD)]
  return (theta3 <@> theta2 <@> CT alpha mu, theta3 <^> theta2 <^> theta1)

-- (l, (x, p, k, c))
inferSc :: [(Name, (Name, Name, Name, Comp))] -> W (CType, Theta)
inferSc [] = do
  alpha <- freshV
  mu <- freshE
  return (CT alpha mu, M.empty)
inferSc ((l, (x, p, k, c)) : scs) = undefined

inferFwd :: Handler -> W (CType, Theta)
inferFwd = undefined

inferC :: Comp -> W (CType, Theta)
inferC (App v1 v2) = do
  (a1, theta1) <- inferV v1
  ctx <- get
  put (theta1 <@> ctx)
  (a2, theta2) <- inferV v2
  put ctx
  alpha <- freshV
  mu <- freshE
  theta3 <- unify (theta2 <@> a1) (TArr a2 (CT alpha mu))
  -- traceM $ "trace: " ++ show (apply theta2 a1) ++ " ||| " ++ show (TArr a2 (CT alpha mu))
  -- traceM $ show (M.lookup "$4" theta3) ++ " ||| " ++ show (M.lookup "$2" theta3)
  return (apply theta3 (CT alpha mu), theta3 <^> theta2 <^> theta1)
inferC (Let x v c) = do
  (a1, theta1) <- inferV v
  sigma <- gen theta1 a1
  ctx <- get
  let nctx = addBinding (apply theta1 ctx) (x, TypeBind sigma)
  put nctx
  (uC, theta2) <- inferC c
  put ctx
  return (uC, theta2 <^> theta1)
inferC (Return v) = do
  (a, theta) <- inferV v
  mu <- freshE
  return (CT a mu, theta)
inferC (Do x c1 c2) = do
  (CT a e, theta1) <- inferC c1
  ctx <- get
  let nctx = addBinding (apply theta1 ctx) (x, TypeBind (Mono a))
  put nctx
  (CT b f, theta2) <- inferC c2
  theta3 <- unify (apply theta2 e) f
  return (CT b (apply theta3 f), theta3 <^> theta2 <^> theta1)
inferC (Handle v c) = do
  (a, theta1) <- inferV v
  ctx <- get
  put (theta1 <@> ctx)
  (uC, theta2) <- inferC c
  put ctx
  alpha <- freshV
  mu <- freshE
  theta3 <- unify (theta2 <@> a) (THand uC (CT alpha mu))
  return (theta3 <@> CT alpha mu, theta3 <^> theta2 <^> theta1)

inferC (Op l v (y :. c)) = do
  (_, (al, bl)) <- name2entry sigma l
  (a, theta1) <- inferV v
  theta2 <- unify (apply theta1 al) a
  ctx <- get
  let nctx = addBinding (apply theta2 (apply theta1 ctx)) (y, TypeBind (Mono bl))
  put nctx
  (CT a' e, theta3) <- inferC c
  put ctx
  mu <- freshE
  theta4 <- unify e (ECons l mu)
  return (apply theta4 $ CT a' e, theta4 <^> theta3 <^> theta2 <^> theta1)

-- TODO: Maybe it is better to give built-in functions types and use T-App to type them
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
