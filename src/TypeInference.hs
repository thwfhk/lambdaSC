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
  return $ TVar ('$' : show i) False

freshE :: W EType
freshE = do
  i <- lift . lift $ get
  lift . lift $ put (i+1)
  return $ EVar ('$' : show i) False

freshTV :: W VType
freshTV = do
  i <- lift . lift $ get
  lift . lift $ put (i+1)
  return $ TVar ('$' : show i) True

freshTE :: W EType
freshTE = do
  i <- lift . lift $ get
  lift . lift $ put (i+1)
  return $ EVar ('$' : show i) True

getVarName :: VType -> Name
getVarName (TVar x _) = x
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
  CompType -> throwError "computation type is not allowed to be quantified"

gen :: Theta -> VType -> W SType
gen theta t = do
  ctx <- get
  let cs = S.unions . map freeVars . onlyTypes $ ctx
  let vs = freeVars t `S.difference` cs
  return (S.foldr (uncurry Forall) (Mono t) vs)


----------------------------------------------------------------
-- type-level reduction

class Reducible a where
  reduce :: a -> a

instance Reducible VType where
  reduce (TApp m t) = applyTyOpt (reduce m) (reduce t)
  reduce (TArr t1 t2) = TArr (reduce t1) (reduce t2)
  reduce (TPair t1 t2) = TPair (reduce t1) (reduce t2)
  reduce (TSum t1 t2) = TSum (reduce t1) (reduce t2)
  reduce (THand t1 t2) = THand (reduce t1) (reduce t2)
  reduce (TMem t1 t2) = TMem (reduce t1) (reduce t2)
  reduce (TList t) = TList (reduce t)
  reduce (TCutList t) = TCutList (reduce t)
  reduce oth = oth

instance Reducible CType where
  reduce (CT t1 t2) = CT (reduce t1) t2

instance Reducible TypeOpt where
  reduce (TAbs x k t) = TAbs x k (reduce t)
  reduce (TNil t) = TNil (reduce t)

isReducible :: (Eq a, Reducible a) => a -> Bool
isReducible t = reduce t /= t
----------------------------------------------------------------
-- unification

class Unifiable a where
  unify :: a -> a -> W Theta

instance Unifiable VType where
  unify t1 t2 | isReducible t1 || isReducible t2 = unify (reduce t1) (reduce t2)
  unify (TApp m t) t' = unify (applyTyOpt m t) t' -- type-level reduction
  unify t' (TApp m t) = unify t' (applyTyOpt m t)
  unify (TVar x b1) (TVar y b2) | x == y && b1 == b2 = return M.empty
  unify (TVar x False) t | x `S.member` S.map fst (freeVars t) =
    throwError "[unification fail] free value type variable appearing in the other type"
  unify (TVar x False) t  = return $ M.singleton x (Left t)
    -- including the case that t is a type variable
  unify t (TVar x False) = unify (TVar x False) t
  unify (TArr t1 c1) (TArr t2 c2) = do
    theta1 <- unify t1 t2
    theta2 <- unify (apply theta1 c1) (apply theta1 c2)
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
  unify t1 t2 = throwError $ "unification undefined for " ++ show t1 ++ " and "  ++ show t2
  -- unify _ _ = undefined

instance Unifiable CType where
  unify (CT t1 e1) (CT t2 e2) = do
    theta1 <- unify t1 t2
    theta2 <- unify (apply theta1 e1) (apply theta1 e2)
    return $ theta2 <^> theta1

-- NOTE: simplification: there is no need to substitute labels
instance Unifiable EType where
  unify EEmpty EEmpty = return M.empty
  unify (EVar x b1) (EVar y b2) | x == y && b1 == b2 = return M.empty
  unify (EVar x False) t | x `S.member` S.map fst (freeVars t) = throwError
    "[unification fail] free effect type variable appearing in the other type"
  unify (EVar x False) t = return $ M.singleton x (Right t)
  unify t (EVar x False) = unify (EVar x False) t
  unify (ECons l t1) t2 = do
    -- traceM $ "unify ECone: " ++ show (ECons l t1) ++ " and " ++ show t2 
    (t3, theta1) <- findLabel l t2
    case tailEffType t1 of
      Nothing -> return ()
      Just x -> when (M.member x theta1) $ throwError "unify EType: tail condition fails"
    theta2 <- unify t1 t3
    return $ theta2 <^> theta1
  unify t2 (ECons l t1) = unify (ECons l t1) t2
  unify t1 t2 = throwError $ "unification undefined for " ++ show t1 ++ " and "  ++ show t2

tailEffType :: EType -> Maybe Name
tailEffType EEmpty = Nothing
tailEffType (EVar x b) = Just x
tailEffType (ECons l t) = tailEffType t

findLabel :: Name -> EType -> W (EType, Theta)
findLabel x EEmpty = throwError $ "findLabel: no label " ++ x ++ " found"
findLabel x (EVar y b) = do
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
inferV (Vchar _) = return (TChar, M.empty)
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
  let m = carrier h

  -- return clause
  (uC1, theta1) <- inferRet h m
  let CT (TApp m' a1) e1 = uC1
  when (m' /= m) $ throwError "infer handler : different carrier"
  case a1 of
    TVar _ False -> return ()
    _ -> throwError "infer handler : the return clause is not polymorphic"
  ctx <- get

  -- op & sc clauses
  put (theta1 <@> ctx)
  (uC2, theta2) <- inferOpr h m
  let CT (TApp m' a2) e2 = uC2
  when (m' /= m) $ throwError "infer handler : different carrier"
  case a2 of
    TVar _ False -> return ()
    _ -> throwError "infer handler : operation clauses are not polymorphic"
  theta3 <- unify (theta2 <@> a1 <!> e1) (a2 <!> e2)

  -- fwd clauses
  let nctx = theta3 <^> theta2 <^> theta1 <@> ctx
  put nctx
  (uC3, theta4) <- inferFwd h m
  let CT (TApp m' a3) e3 = uC3
  when (m' /= m) $ throwError "infer handler : different carrier"
  case a3 of
    TVar _ False -> return ()
    _ -> throwError "infer handler : operation clauses are not polymorphic"
  theta5 <- unify (theta4 <^> theta3 <@> a2 <!> e2) (a3 <!> e3)
  put ctx

  let theta = theta5 <^> theta4 <^> theta3 <^> theta2 <^> theta1
  let a4 = theta5 <@> a3
  when (S.member (getVarName a4, ValueType) (freeVars $ theta5 <^> theta4 <@> nctx)) $
    throwError "infer handler : handler is not polymorphic"

  when (freeVars m `S.intersection` freeVars (theta <@> ctx) /= S.empty) $ do
    throwError "infer handler : free variables in M will escape"

  let f = appendEff (oplist h ++ sclist h) (theta5 <@> e3)
  return (THand (a4 <!> f) (theta5 <@> TApp m a4 <!> e3), theta)

inferV oth = error $ "inferV undefined for " ++ show oth

inferRet :: Handler -> TypeOpt -> W (CType, Theta)
inferRet h m = do
  let (x, cr) = hreturn h
  alpha <- freshV
  mu <- freshE
  ctx <- get
  put (addBinding ctx (x, TypeBind $ Mono alpha))
  (uC, theta1) <- inferC cr
  theta2 <- unify uC (theta1 <@> TApp m alpha <!> mu)
  put ctx
  return (theta2 <^> theta1 <@> TApp m alpha <!> mu, theta2 <^> theta1)

-- | operation clauses
inferOpr :: Handler -> TypeOpt -> W (CType, Theta)
inferOpr h m = do
  (uC1, theta1) <- inferOp m ops -- also need the carrier
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

inferEmp :: TypeOpt -> W (CType, Theta)
inferEmp m = do
  alpha <- freshV
  mu <- freshE
  return (TApp m alpha <!> mu, M.empty)

-- (l, (x, k, c))
inferOp :: TypeOpt -> [(Name, (Name, Name, Comp))] -> W (CType, Theta)
inferOp m [] = inferEmp m
inferOp m ((l, (x, k, c)) : ops) = do
  when (isSc l) . throwError $ "inferOp : " ++ l ++ " is not an algebraic operation"
  (_, (al, bl)) <- name2entry sigma l
  (uD, theta1) <- inferOp m ops
  let CT (TApp m' a) e = uD -- if not, an error will be throwed
  m <- return $ theta1 <@> m
  when (m' /= m) $ throwError "inferOp : different carrier"
  ctx <- get
  let nctx = addBindings (theta1 <@> ctx)
        [ (x, TypeBind $ Mono al)
        , (k, TypeBind . Mono $ TArr bl uD)]
  put nctx
  (uC, theta2) <- inferC c
  put ctx
  theta3 <- unify uC (theta2 <@> uD)
  return (theta3 <^> theta2 <@> uD, theta3 <^> theta2 <^> theta1)

-- (l, (x, p, k, c))
inferSc :: TypeOpt -> [(Name, (Name, Name, Name, Comp))] -> W (CType, Theta)
inferSc m [] = inferEmp m
inferSc m ((l, (x, p, k, c)) : scs) = do
  when (isOp l) . throwError $ "inferSc : " ++ l ++ " is not a scoped operation"
  (_, (al, bl)) <- name2entry sigma l
  beta <- freshTV -- fresh value type variable
  (uD, theta1) <- inferSc m scs
  let CT (TApp m' a) e = uD
  m <- return $ theta1 <@> m
  when (m' /= m) $ throwError "inferSc : different carrier"
  ctx <- get
  let nctx = addBindings (theta1 <@> ctx)
        [ (x, TypeBind $ Mono al)
        -- , (p, TypeBind . Mono $ TArr bl (CT (applyTyOpt m beta) mu))
        , (p, TypeBind . Mono $ TArr bl (TApp m beta <!> e))
        , (k, TypeBind . Mono $ TArr beta uD) ]
  put nctx
  (uC, theta2) <- inferC c
  put ctx
  theta3 <- unify uC (theta2 <@> uD)
  -- beta notin dom(theta2 <^> theta1)
  when (M.member (getVarName beta) (theta3 <^> theta2 <^> theta1)) $
    throwError "inferSc: beta is substituted"
  -- when (M.member (getVarName beta) (theta3 <^> theta2 <^> theta1)) $ do
  --     -- 因为没有区分type variable和unification variable，所以先允许被替换成其他variable
  --     let t = M.lookup (getVarName beta) (theta3 <^> theta2 <^> theta1)
  --     case t of
  --       Nothing -> return ()
  --       Just (Left (TVar _ _)) -> return()
  --       Just _ -> throwError "inferSc: beta is substituted"
  return (theta3 <^> theta2 <@> uD, theta3 <^> theta2 <^> theta1)


inferFwd :: Handler -> TypeOpt -> W (CType, Theta)
inferFwd h m = do
  let (f, p, k, cf) = hfwd h
  alpha <- freshTV
  beta <- freshTV
  gamma <- freshTV
  delta <- freshTV
  mu <- freshE
  alpha' <- freshV
  -- let ap  = alpha <->> applyTyOpt m beta <!> mu
  -- let ak  = beta <->> applyTyOpt m alpha' <!> mu
  let ap  = alpha <->> TApp m beta <!> mu
  let ak  = beta <->> TApp m alpha' <!> mu
  let ap' = alpha <->> gamma <!> mu
  let ak' = gamma <->> delta <!> mu
  ctx <- get
  let nctx = addBindings ctx
        [ (f, TypeBind . Forall (getVarName gamma) ValueType . Forall (getVarName delta) ValueType . Mono
                $ TPair ap' ak' <->> delta <!> mu)
        , (p, TypeBind $ Mono ap)
        , (k, TypeBind $ Mono ak) ] -- NOTE: the order f, p, k cannot be changed!
  put nctx
  (uC, theta1) <- inferC cf
  put ctx
  theta2 <- unify uC (theta1 <@> TApp m alpha' <!> mu)
  when (  M.member (getVarName alpha) (theta2 <^> theta1) 
       || M.member (getVarName beta) (theta2 <^> theta1)
       || M.member (getVarName gamma) (theta2 <^> theta1)
       || M.member (getVarName delta) (theta2 <^> theta1)
       ) $
    throwError "inferFwd: type variables are substituted"
  return (theta2 <^> theta1 <@> TApp m alpha' <!> mu, theta2 <^> theta1)

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
inferC (LetRec x v c) = do
  alpha <- freshV
  ctx <- get
  put $ addBinding ctx (x, TypeBind $ Mono alpha)
  (a, theta1) <- inferV v
  theta2 <- unify (theta1 <@> alpha) a
  sigma <- gen (theta2 <^> theta1) (theta2 <@> a)
  put $ addBinding (theta2 <^> theta1 <@> ctx) (x, TypeBind sigma)
  (uC, theta3) <- inferC c
  put ctx
  return (uC, theta3 <^> theta2 <^> theta1)
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
inferC (Anytype c) = do
  alpha <- freshV
  mu <- freshE
  return (alpha <!> mu, M.empty)
inferC (Undefined _) = do
  alpha <- freshV
  mu <- freshE
  return (alpha <!> mu, M.empty)


inferC (Op l v (y :. c)) = do
  when (isSc l) . throwError $ "inferOp : " ++ l ++ " is not an algebraic operation"
  (_, (al, bl)) <- name2entry sigma l
  (a, theta1) <- inferV v
  theta2 <- unify al a
  ctx <- get
  let nctx = addBinding (theta2 <@> theta1 <@> ctx) (y, TypeBind (Mono bl))
  put nctx
  (CT a' e, theta3) <- inferC c
  put ctx
  mu <- freshE
  theta4 <- unify e (ECons l mu)
  return (theta4 <@> a' <!> e, theta4 <^> theta3 <^> theta2 <^> theta1)

inferC (Sc l v (y :. c1) (z :. c2)) = do
  when (isOp l) . throwError $ "inferOp : " ++ l ++ " is not a scoped operation"
  (_, (al, bl)) <- name2entry sigma l
  (a, theta1) <- inferV v
  theta2 <- unify al a
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
inferC (Mul v1 v2) = inferFunc2 "mul" v1 v2
inferC (Eq v1 v2) = inferFunc2 "eq" v1 v2
inferC (Lt v1 v2) = inferFunc2 "lt" v1 v2
inferC (Fst v) = inferFunc1 "fst" v
inferC (Snd v) = inferFunc1 "snd" v
inferC (Head v) = inferFunc1 "head" v
inferC (Tail v) = inferFunc1 "tail" v
inferC (Read v) = inferFunc1 "read" v
inferC (Cons v1 v2) = inferFunc2 "cons" v1 v2
inferC (Append v1 v2) = inferFunc2 "append" v1 v2
inferC (AppendCut v1 v2) = inferFunc2 "appendCut" v1 v2
-- inferC (ConcatMap v1 v2) = inferFunc2 "concatMap" v1 v2
inferC (ConcatMapCutList v1 v2) = inferFunc2 "concatMapCutList" v1 v2
inferC (Newmem v) = inferFunc1 "newmem" v
inferC (Update v1 v2) = inferFunc2 "update" v1 v2
inferC (Retrieve v1 v2) = inferFunc2 "retrieve" v1 v2
inferC (Open v) = inferFunc1 "open" v
inferC (Close v) = inferFunc1 "close" v
inferC (IsClose v) = inferFunc1 "isclose" v

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

----------------------------------------------------------------

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
