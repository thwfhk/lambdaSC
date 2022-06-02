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

getVarName :: VType -> Name
getVarName (TVar x) = x
getVarName oth = error "getVarName: not a variable"

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
  unify (TVar x) t | x `S.member` S.map fst (freeVars t) =
    trace ("[[[ " ++ show (TVar x) ++ " ||| " ++ show t ++ " ]]]") $
    throwError
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
  unify (TMem t1 t2) (TMem t1' t2') = do
    theta1 <- unify t1 t1'
    theta2 <- unify (apply theta1 t2) (apply theta1 t2')
    return $ theta2 <^> theta1
  unify (TSum t1 t2) (TSum t1' t2') = do
    theta1 <- unify t1 t1'
    theta2 <- unify (apply theta1 t2) (apply theta1 t2')
    return $ theta2 <^> theta1
  unify (THand t1 t2) (THand t1' t2') = do
    theta1 <- unify t1 t1'
    theta2 <- unify (apply theta1 t2) (apply theta1 t2')
    return $ theta2 <^> theta1
  unify (TList t) (TList t') = unify t t'
  unify (TCutList t) (TCutList t') = unify t t'
  unify t1 t2 | t1 == t2 = return M.empty
  unify t1 t2 = error $ "unification undefined for " ++ show t1 ++ " and "  ++ show t2
  -- unify _ _ = undefined

instance Unifiable CType where
  unify (CT t1 e1) (CT t2 e2) = do
    theta1 <- unify t1 t2
    theta2 <- unify (apply theta1 e1) (apply theta1 e2)
    return $ theta2 <^> theta1

-- NOTE: simplification: there is no need to substitute labels
instance Unifiable EType where
  unify EEmpty EEmpty = return M.empty
  unify (EVar x) (EVar y) | x == y = return M.empty
  unify (EVar x) t | x `S.member` S.map fst (freeVars t) = throwError
    "[unification fail] free effect type variable appearing in the other type"
  unify (EVar x) t  = return $ M.singleton x (Right t)
  unify t (EVar x) = unify (EVar x) t
  unify (ECons l t1) t2 = do
    -- traceM $ "unify ECone: " ++ show (ECons l t1) ++ " and " ++ show t2 
    (t3, theta1) <- findLabel l t2
    case tailEffType t1 of
      Nothing -> return ()
      Just x -> when (M.member x theta1) $ throwError "unify EType: tail condition fails"
    theta2 <- unify t1 t3
    return $ theta2 <^> theta1
  unify t2 (ECons l t1) = unify (ECons l t1) t2

tailEffType :: EType -> Maybe Name
tailEffType EEmpty = Nothing
tailEffType (EVar x) = Just x
tailEffType (ECons l t) = tailEffType t

findLabel :: Name -> EType -> W (EType, Theta)
findLabel x EEmpty = throwError $ "findLabel: no label " ++ x ++ " found"
findLabel x (EVar y) = do
  mu <- freshE
  let theta = M.singleton y (Right $ ECons x mu)
  return (mu, theta)
findLabel x (ECons l t) = if l == x then return (t, M.empty)
                          else do (t', theta) <- findLabel x t;
                                  return (ECons l t', theta)

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
  sigma <- index2type ctx n
  tau <- inst sigma
  return (tau, M.empty)
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
inferV (Vstr _) = return (TString, M.empty)
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
inferV (Vret v) = do
  (a, theta) <- inferV v
  case a of TList t -> return (TCutList t, theta)
            _ -> throwError "opened should take a list"
inferV (Vflag v) = do
  (a, theta) <- inferV v
  case a of TList t -> return (TCutList t, theta)
            _ -> throwError "closed should take a list"
inferV (Vsum (Left v)) = do
  (a, theta) <- inferV v
  alpha <- freshV
  return (TSum a alpha, theta)
inferV (Vsum (Right v)) = do
  (a, theta) <- inferV v
  alpha <- freshV
  return (TSum alpha a, theta)

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
  (uC'', theta3) <- inferFwd h
  put ctx
  let m = carrier h
  let uD = theta3 <@> theta2 <@> theta1 <@> CT (applyTyOpt m alpha) mu
  theta4 <- unifyList [(theta3 <@> theta2 <@> uC, uD), (theta3 <@> uC', uD), (uC'', uD)]
  let theta = theta4 <^> theta3 <^> theta2 <^> theta1
  return (theta <@> THand (CT alpha f) (CT (applyTyOpt m alpha) mu), theta)

inferV oth = error $ "inferV undefined for " ++ show oth

-- | operation clauses
inferOpr :: Handler -> W (CType, Theta)
inferOpr h = do
  let m = carrier h
  (uC1, theta1) <- inferOp ops
  ctx <- get
  put (theta1 <@> ctx)
  (uC2, theta2) <- inferSc m scs -- need the carrier
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
inferSc :: TypeOpt -> [(Name, (Name, Name, Name, Comp))] -> W (CType, Theta)
inferSc _ [] = do
  alpha <- freshV
  mu <- freshE
  return (CT alpha mu, M.empty)
inferSc m ((l, (x, p, k, c)) : scs) = do
  (_, (al, bl)) <- name2entry sigma l
  alpha <- freshV
  beta <- freshV
  mu <- freshE
  (uD, theta1) <- inferSc m scs
  ctx <- get
  let nctx = addBindings (theta1 <@> ctx)
        [ (x, TypeBind $ Mono al)
        , (p, TypeBind . Mono $ TArr bl (CT (applyTyOpt m beta) mu))
        , (k, TypeBind . Mono $ TArr beta (CT alpha mu)) ]
  put nctx
  (uC, theta2) <- inferC c
  put ctx
  theta3 <- unifyList [(theta2 <@> CT alpha mu, uC), (theta2 <@> CT alpha mu, theta2 <@> uD)]
  return (theta3 <@> theta2 <@> CT alpha mu, theta3 <^> theta2 <^> theta1)


inferFwd :: Handler -> W (CType, Theta)
inferFwd h = do
  let m = carrier h
  let (f, p, k, cf) = hfwd h
  alpha <- freshV
  beta <- freshV
  gamma <- freshV
  gamma' <- freshV
  mu <- freshE
  alpha' <- freshV
  -- traceM $ "look: " ++ getVarName alpha ++ " " ++ getVarName alpha'
  let ap  = alpha <->> applyTyOpt m beta <!> mu
  let ap' = alpha <->> gamma <!> mu
  let ak  = beta <->> applyTyOpt m alpha' <!> mu
  -- let ak' = gamma <->> applyTyOpt m alpha' mu <!> mu
  let ak' = gamma <->> gamma' <!> mu
  ctx <- get
  let nctx = addBindings ctx
        [ (f, TypeBind . Forall (getVarName gamma) ValueType . Forall (getVarName gamma') ValueType . Mono
                $ TPair ap' ak' <->> gamma' <!> mu)
        , (p, TypeBind $ Mono ap)
        , (k, TypeBind $ Mono ak) ] -- NOTE: the order f, p, k cannot be changed!
  put nctx
  -- traceM "hi!!!!!!!!!"
  (uC, theta1) <- inferC cf
  -- traceM "end!!!!!!!!!"
  put ctx
  -- traceM $ "### " ++ show uC ++ "\n### " ++ show (theta1 <@> applyTyOpt m alpha' mu <!> mu)
  -- traceM $ "m: " ++ show m
  theta2 <- unify uC (theta1 <@> applyTyOpt m alpha' <!> mu)
  return (theta2 <@> uC, theta2 <^> theta1)

inferC :: Comp -> W (CType, Theta)
inferC (App v1 v2) = do
  -- traceM $ "app: " ++ show v1 ++ " | "  ++ show v2
  (a1, theta1) <- inferV v1
  ctx <- get
  put (theta1 <@> ctx)
  (a2, theta2) <- inferV v2
  put ctx
  alpha <- freshV
  mu <- freshE
  -- traceM $ "[inferC App]: " ++ show (theta2 <@> a1) ++ " || " ++ show (TArr a2 (CT alpha mu))
  -- traceM $ "before unify: " ++ show v1
  -- when (show v1 == "Var \"f\" 3") $ traceM $ "### " ++ show (theta2 <@> a1) ++ "\n### " ++ show (TArr a2 (CT alpha mu))
  theta3 <- unify (theta2 <@> a1) (TArr a2 (CT alpha mu))
  -- traceM $ "endapp: " ++ show v1
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
  put ctx
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
inferC (If v c1 c2) = do
  (a, theta1) <- inferV v
  theta2 <- unify a TBool
  ctx <- get
  put (theta2 <@> theta1 <@> ctx)
  (uC, theta3) <- inferC c1
  put (theta3 <@> theta2 <@> theta1 <@> ctx)
  (uD, theta4) <- inferC c2
  theta5 <- unify (theta4 <@> uC) uD
  return (theta5 <@> uD, theta5 <^> theta4 <^> theta3 <^> theta2 <^> theta1)
inferC (Case v x c1 y c2) = do
  (a, theta1) <- inferV v
  alpha <- freshV
  beta <- freshV
  theta2 <- unify a (TSum alpha beta)
  ctx <- get
  put $ addBinding (theta2 <@> theta1 <@> ctx) (x, TypeBind . Mono $ theta2 <@> alpha)
  (uC, theta3) <- inferC c1
  put $ addBinding (theta3 <@> theta2 <@> theta1 <@> ctx) (x, TypeBind . Mono $ theta3 <@> theta2 <@> beta)
  (uD, theta4) <- inferC c2
  theta5 <- unify (theta4 <@> uC) uD
  return (theta5 <@> uD, theta5 <^> theta4 <^> theta3 <^> theta2 <^> theta1)
inferC (Absurd v) = do
  (a, theta1) <- inferV v
  theta2 <- unify a TEmpty
  alpha <- freshV
  mu <- freshE
  return (alpha <!> mu, theta2 <^> theta1)


inferC (Op l v (y :. c)) = do
  (_, (al, bl)) <- name2entry sigma l
  (a, theta1) <- inferV v
  theta2 <- unify (theta1 <@> al) a
  ctx <- get
  let nctx = addBinding (theta2 <@> theta1 <@> ctx) (y, TypeBind (Mono bl))
  put nctx
  (CT a' e, theta3) <- inferC c
  put ctx
  mu <- freshE
  theta4 <- unify e (ECons l mu)
  return (theta4 <@> a' <!> e, theta4 <^> theta3 <^> theta2 <^> theta1)

inferC (Sc l v (y :. c1) (z :. c2)) = do
  (_, (al, bl)) <- name2entry sigma l
  (a, theta1) <- inferV v
  theta2 <- unify (theta1 <@> al) a
  ctx <- get
  let nctx = addBinding (theta2 <@> theta1 <@> ctx) (y, TypeBind (Mono bl))
  put nctx
  (CT b e, theta3) <- inferC c1
  mu <- freshE
  theta4 <- unify e (ECons l mu)
  let nctx = addBinding (theta4 <@> theta3 <@> theta2 <@> theta1 <@> ctx) (z, TypeBind (Mono b))
  put nctx
  (CT a' f, theta5) <- inferC c2
  put ctx
  theta6 <- unify f (theta4 <@> theta5 <@> ECons l mu)
  return (theta6 <@> a' <!> f, theta6 <^> theta5 <^> theta4 <^> theta3 <^> theta2 <^> theta1)


-- inferC (Fst v) = do
--   (a, theta1) <- inferV v
--   alpha1 <- freshV
--   alpha2 <- freshV
--   theta2 <- unify a (TPair alpha1 alpha2)
--   mu <- freshE
--   return (CT (apply theta2 alpha1) mu, theta2 <^> theta1)
inferC (Add v1 v2) = inferFunc2 "add" v1 v2
inferC (Minus v1 v2) = inferFunc2 "minus" v1 v2
inferC (Eq v1 v2) = inferFunc2 "eq" v1 v2
inferC (Lt v1 v2) = inferFunc2 "lt" v1 v2
inferC (Fst v) = inferFunc1 "fst" v
inferC (Snd v) = inferFunc1 "snd" v
inferC (Head v) = inferFunc1 "head" v
inferC (Append v1 v2) = inferFunc2 "append" v1 v2
inferC (AppendCut v1 v2) = inferFunc2 "appendCut" v1 v2
inferC (ConcatMap v1 v2) = inferFunc2 "concatMap" v1 v2
inferC (ConcatMapCutList v1 v2) = inferFunc2 "concatMapCutList" v1 v2
inferC (Newmem v) = inferFunc1 "newmem" v
inferC (Update v1 v2) = inferFunc2 "update" v1 v2
inferC (Retrieve v1 v2) = inferFunc2 "retrieve" v1 v2
inferC (Open v) = inferFunc1 "open" v
inferC (Close v) = inferFunc1 "close" v

inferC oth = error $ "inferC undefined for " ++ show oth

inferFunc1 :: Name -> Value -> W (CType, Theta)
inferFunc1 name v = do
  (a, theta1) <- inferV v
  -- when (name == "fst") $ traceM $ "fst : " ++ show a
  -- when (name == "snd") $ traceM $ "snd : " ++ show a
  ctx <- get
  put (theta1 <@> ctx)
  -- (uC, theta2) <- inferC $ App (Var name 0) v
  (uC, theta2) <- specialTApp (builtInFuncType name) v
  put ctx
  return (uC, theta2 <^> theta1)

inferFunc2 :: Name -> Value -> Value -> W (CType, Theta)
inferFunc2 name v1 v2 = do
  (a, theta1) <- inferV (Vpair (v1, v2))
  ctx <- get
  put (theta1 <@> ctx)
  -- (uC, theta2) <- inferC $ App (Var name 0) (Vpair (v1, v2))
  (uC, theta2) <- specialTApp (builtInFuncType name) (Vpair (v1, v2))
  put ctx
  return (uC, theta2 <^> theta1)

specialTApp :: SType -> Value -> W (CType, Theta)
specialTApp sigma v2 = do
  a1 <- inst sigma
  (a2, theta2) <- inferV v2
  alpha <- freshV
  mu <- freshE
  theta3 <- unify (theta2 <@> a1) (TArr a2 (CT alpha mu))
  return (apply theta3 (CT alpha mu), theta3 <^> theta2)