{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use when" #-}

module Syntax where

import Control.Monad.Except
import Data.List
import qualified Data.Set as S

type Err = String
type Name = String


-- | Command syntax
data Command
  = Def Name Value
  | Run Comp
  deriving (Show, Eq)

-- | Value syntax
data Value
  = Var Name Int  -- ^ use De Bruijn Index
  | Lam Name Comp
  | Vunit
  | Vpair (Value, Value)
  | Vhandler Handler
  -- extensions:
  | Vbool Bool
  | Vint Int
  | Vchar Char
  | Vstr String   -- ^ for simplicity, we separate lists and strings
  | Vlist [Value]
  | Vsum (Either Value Value)
  | Vret Value | Vflag Value -- opened, closed
  | Vmem (Memory Value)
  deriving (Show, Eq)

-- | Handler Clauses Syntax
data Clause
  = RetClause Name Comp
  | OpClause Name Name Name Comp
  | ScClause Name Name Name Name Comp
  | FwdClause Name Name Name Comp
  deriving (Show, Eq)


-- | Handler syntax
data Handler = Handler
  { hname   :: Name                                   -- ^ handler name
  , carrier :: TypeOpt                                -- ^ type operator M
  , oplist  :: [Name]                                 -- ^ algberaic operations names
  , sclist  :: [Name]                                 -- ^ scoped operations names
  , hreturn :: (Name, Comp)                           -- ^ (x, c)
  , hop     :: Name -> Maybe (Name, Name, Comp)       -- ^ l -> (x, k, c)
  , hsc     :: Name -> Maybe (Name, Name, Name, Comp) -- ^ l -> (x, p, k, c)
  , hfwd    :: (Name, Name, Name, Comp)               -- ^ (f, p, k, c)
  }
instance Show Handler where
  show (Handler name _ _ _ _ _ _ _) = "handler{" ++ name ++ "}"

instance Eq Handler where
  Handler x _ _ _ _ _ _ _ == Handler y _ _ _ _ _ _ _ = x == y

infixr 0 :.
data (Dot a b) = a :. b deriving (Show, Eq)

-- | Computation syntax
data Comp
  = Return Value                                   -- ^ return v
  | Op Name Value (Dot Name Comp)                  -- ^ op l v (y.c)
  | Sc Name Value (Dot Name Comp) (Dot Name Comp)  -- ^ sc l v (y.c1) (z.c2)
  | Handle Value Comp                              -- ^ v ★ c
  | Do Name Comp Comp                              -- ^ do x <- c1; c2
  | App Value Value                                -- ^ v1 v2
  | Let Name Value Comp                            -- ^ let x = v in c
  -- syntactic sugars:
  | App' [Value]
  -- extensions:
  -- We implement most functions in the paper as built-in functions
  -- because the interpreter doesn't support pattern matching and recursive functions.
  | If Value Comp Comp
  | Case Value Name Comp Name Comp
  | Eq Value Value
  | Lt Value Value
  | Add Value Value
  | Minus Value Value
  | Min Value Value
  | Mul Value Value
  | Append Value Value
  | Head Value
  | Tail Value
  | Fst Value | Snd Value
  | AppendS Value Value
  | HeadS Value
  | TailS Value
  | ConsS Value Value
  | Read Value
  | ConcatMap Value Value
  | AppendCut Value Value
  | ConcatMapCutList Value Value
  | Close Value | Open Value
  | Retrieve Value Value
  | Update Value Value
  | Newmem Value
  | Absurd Value
  deriving (Show, Eq)

infixr 8 #
(#) :: Value -> Comp -> Comp
h # c = Handle h c

----------------------------------------------------------------
-- type syntax

-- If you add a new built-in type, you may need to modify:
-- 1. class Applicable
-- 2. class Unifiable
-- 3. class SubstValueType & SubstEffectType

-- value type
data VType
  = TVar Name Bool -- name, true : type variable / false : unification variable
  | TArr VType CType
  | TPair VType VType
  | TSum VType VType
  | THand CType CType
  | TList VType
  | TCutList VType
  | TMem VType VType
  | TUnit
  | TString
  | TBool
  | TInt
  | TEmpty
  | TApp TypeOpt VType
  deriving (Show, Eq)

data CType = CT VType EType
  deriving (Show, Eq)

(<!>) = CT

infixr 8 <->>
(<->>) = TArr

data EType
  = EVar Name Bool -- name, true : type variable / false : unification variable
  | EEmpty
  | ECons Name EType
  deriving (Show, Eq)

-- type scheme
data SType
  = Mono VType
  | Forall Name Kind SType
  deriving (Show, Eq)

data Kind
  = ValueType
  | EffectType
  | CompType
  deriving (Show, Eq, Ord)

type Type = Either VType EType

-- data TypeOpt
--   = TAbs Name VType -- NOTE: fix the form to |lambda alpha . A|, i.e. kind |*->*|
--   deriving (Show, Eq)

data TypeOpt
  = TAbs Name Kind TypeOpt
  | TNil VType
  deriving (Show, Eq)

-- applyTyOpt :: TypeOpt -> VType -> EType -> VType
-- applyTyOpt ty vt et = let (TNil res) = applyTyOptE (applyTyOptV ty vt) et in res

applyTyOpt :: TypeOpt -> VType -> VType
applyTyOpt ty vt = let (TNil res) = applyTyOptV ty vt in res

applyTyOptV :: TypeOpt -> VType -> TypeOpt
applyTyOptV (TNil _) t = error "applyTyOpt : not applicable"
applyTyOptV (TAbs x k t') t = if k /= ValueType then error "kind mismatch"
                              else substVT (x, t) t'

applyTyOptE :: TypeOpt -> EType -> TypeOpt
applyTyOptE (TNil _) t = error "applyTyOpt : not applicable"
applyTyOptE (TAbs x k t') t = if k /= EffectType then error "kind mismatch"
                              else substET (x, t) t'

-- only need to substitute a value type into other types
class SubstValueType a where
  substVT :: (Name, VType) -> a -> a
class SubstEffectType a where
  substET :: (Name, EType) -> a -> a

instance SubstValueType TypeOpt where
  substVT (x, t) (TNil t') = TNil $ substVT (x, t) t'
  substVT (x, t) (TAbs y k t') | x == y = TAbs y k t'
  substVT (x, t) (TAbs y k t') | x /= y = TAbs y k (substVT (x, t) t')

instance SubstEffectType TypeOpt where
  substET (x, t) (TNil t') = TNil $ substET (x, t) t'
  substET (x, t) (TAbs y k t') | x == y = TAbs y k t'
  substET (x, t) (TAbs y k t') | x /= y = TAbs y k (substET (x, t) t')

instance SubstValueType VType where
  substVT (x, t) a = case a of
    TVar y _ | x == y -> t
    TVar y b | x /= y -> TVar y b
    TArr t1 (CT t2 e) -> TArr (substVT (x, t) t1) (CT (substVT (x, t) t2) e)
    TPair t1 t2 -> TPair (substVT (x, t) t1) (substVT (x, t) t2)
    TMem t1 t2 -> TMem (substVT (x, t) t1) (substVT (x, t) t2)
    TSum t1 t2 -> TSum (substVT (x, t) t1) (substVT (x, t) t2)
    TList ts -> TList (substVT (x, t) ts)
    TCutList ts -> TCutList (substVT (x, t) ts)
    TString -> TString
    TUnit -> TUnit
    TBool -> TBool
    TInt -> TInt
    TEmpty -> TEmpty
    THand t1 t2 -> error "Are you serious?"
    -- oth -> error $ "substVT undefined for " ++ show oth

instance SubstEffectType VType where
  substET (x, t) a = case a of
    TVar y b -> TVar y b
    TArr t1 (CT t2 e) -> TArr (substET (x, t) t1) (CT (substET (x, t) t2) (substET (x, t) e))
    TPair t1 t2 -> TPair (substET (x, t) t1) (substET (x, t) t2)
    TMem t1 t2 -> TMem (substET (x, t) t1) (substET (x, t) t2)
    TSum t1 t2 -> TSum (substET (x, t) t1) (substET (x, t) t2)
    TList ts -> TList (substET (x, t) ts)
    TCutList ts -> TCutList (substET (x, t) ts)
    TString -> TString
    TUnit -> TUnit
    TBool -> TBool
    TInt -> TInt
    TEmpty -> TEmpty
    THand t1 t2 -> error "Are you serious?"
    -- oth -> error $ "substET undefined for " ++ show oth

instance SubstEffectType EType where
  substET (x, t) a = case a of
    EEmpty -> EEmpty
    EVar y _ | x == y -> t
    EVar y b | x /= y -> EVar y b
    ECons l e -> ECons l (substET (x, t) e)
    -- non-exhaustive ??

----------------------------------------------------------------
-- Free type variables and their kinds

class FreeVars a where
  freeVars :: a -> S.Set (Name, Kind)

instance FreeVars VType where
  freeVars (TVar x _) = S.singleton (x, ValueType)
  freeVars (TArr t1 t2) = freeVars t1 `S.union` freeVars t2
  freeVars (TPair t1 t2) = freeVars t1 `S.union` freeVars t2
  freeVars (TSum t1 t2) = freeVars t1 `S.union` freeVars t2
  freeVars (THand t1 t2) = freeVars t1 `S.union` freeVars t2
  freeVars (TList t) = freeVars t
  freeVars _ = S.empty

instance FreeVars SType where
  freeVars (Mono t) = freeVars t
  freeVars (Forall x k t) = S.delete (x, k) (freeVars t)

instance FreeVars CType where
  freeVars (CT t1 t2) = freeVars t1 `S.union` freeVars t2

instance FreeVars EType where
  freeVars (EVar x _) = S.singleton (x, EffectType)
  freeVars (ECons _ t2) = freeVars t2
  freeVars EEmpty = S.empty

instance FreeVars Type where
  freeVars (Left t) = freeVars t
  freeVars (Right t) = freeVars t

instance FreeVars TypeOpt where
  freeVars (TNil vt) = freeVars vt
  freeVars (TAbs x k t) = S.delete (x, k) (freeVars t)
----------------------------------------------------------------
-- built-in functions

-- (name, constructor)
builtInFunc1 :: [(String, Value -> Comp)]
builtInFunc1 =
  [ ("head", Head)
  , ("tail", Tail)
  , ("fst", Fst)
  , ("snd", Snd)
  , ("absurd", Absurd)
  , ("newmem", Newmem)
  , ("open", Open)
  , ("close", Close)
  , ("read", Read)
  ]

-- (name, constructor, is infix)
builtInFunc2 :: [(String, Value -> Value -> Comp, Bool)]
builtInFunc2 =
  [ ("concatMap", ConcatMap, False)
  , ("concatMapCutList", ConcatMapCutList, False)
  , ("update", Update, False)
  , ("retrieve", Retrieve, False)
  , ("append", AppendCut, False)
  , ("++", Append, True)
  , ("+", Add, True)
  , ("-", Minus, True)
  , ("*", Mul, True)
  , ("==", Eq, True)
  , (">", Lt, True)
  ]

-- 这里用相同的"alpha", "beta"应该会造成问题，一个地方同时用多个函数时，unification会以为"alpha"都是同一个
builtInFuncType :: Name -> SType
builtInFuncType s = case s of
  "add" -> fmu s . Mono $ TPair TInt TInt <->> TInt <!> mu s
  "minus" -> fmu s . Mono $ TPair TInt TInt <->> TInt <!> mu s
  "eq" -> fa s . fmu s . Mono $ TPair (a s) (a s)  <->> TBool <!> mu s
  "lt" -> fa s . fmu s . Mono $ TPair (a s) (a s)  <->> TBool <!> mu s
  "fst" -> fa s . fb s . fmu s . Mono $ TPair (a s) (b s) <->> a s <!> mu s
  "snd" -> fa s . fb s . fmu s . Mono $ TPair (a s) (b s) <->> b s <!> mu s
  "head" -> fa s . fmu s . Mono $ TList (a s) <->> a s <!> mu s
  "append" -> fa s . fmu s . Mono $ TPair (TList (a s)) (TList (a s)) <->> TList (a s) <!> mu s
  "concatMap" -> fa s . fb s . fmu s . Mono $
    TPair (TList (b s)) (b s <->> TList (a s) <!> mu s) <->> TList (a s) <!> mu s
  "newmem" -> fa s . fb s . fmu s . Mono $ TUnit <->> TMem (a s) (b s) <!> mu s
  "retrieve" -> fa s . fb s . fmu s . Mono $ TPair (a s) (TMem (a s) (b s)) <->> b s <!> mu s
  "update" -> fa s . fb s . fmu s . Mono $
      TPair (TPair (a s) (b s)) (TMem (a s) (b s)) <->> TMem (a s) (b s) <!> mu s
  "close" -> fa s . fmu s . Mono $ TCutList (a s) <->> TCutList (a s) <!> mu s
  "open" -> fa s . fmu s . Mono $ TCutList (a s) <->> TCutList (a s) <!> mu s
  "appendCut" -> fa s . fmu s . Mono $ TPair (TCutList (a s)) (TCutList (a s)) <->> TCutList (a s) <!> mu s
  "concatMapCutList" -> fa s . fb s . fmu s . Mono $
    TPair (TCutList (b s)) (b s <->> TCutList (a s) <!> mu s) <->> TCutList (a s) <!> mu s
  oth -> error $ "builtInFuncTypes: no " ++ oth ++ " function"
  where
    fa s = Forall ("alpha_" ++ s) ValueType
    fb s = Forall ("beta_" ++ s) ValueType
    fmu s = Forall ("mu_" ++ s) EffectType
    a s = TVar ("alpha_" ++ s) True
    b s = TVar ("beta_" ++ s) True
    mu s = EVar ("mu_" ++ s) True

----------------------------------------------------------------
-- Utilities

appendEff :: [Name] -> EType -> EType
appendEff [] e = e
appendEff ls e = appendEff (init ls) (ECons (last ls) e)

cmds2comps :: [Command] -> [Comp]
cmds2comps cmds =
    let defs = filter isDef cmds
    in let runs = filter isRun cmds
    in map (\ (Run main) -> foldr (\(Def x v) c -> Let x v c) main defs) runs
  where
    isDef (Def _ _) = True
    isDef _ = False
    isRun (Run _) = True
    isRun _ = False


-- 在这里检查语句的种类和数量
-- ret, op, op, op, sc, sc, sc, fwd
clauses2handler :: MonadError Err m => [Clause] -> TypeOpt -> m Handler
clauses2handler cls tyopt = do
    let hname = show cls
    hreturn <- case head cls of
                RetClause x c -> return (x, c)
                _ -> throwError "No return clause"
    hfwd    <- case last cls of
                FwdClause f p k c -> return (f, p, k, c)
                _ -> throwError "No forwarding clause"
    let opCls  = takeWhile isOp (tail cls)
    let oplist = map (\(OpClause l _ _ _) -> l) opCls
    let hop    = \name ->
          do OpClause _ x k c <- find (\(OpClause l _ _ _) -> l == name) opCls
             return (x, k, c)
    let scCls  = takeWhile isSc (reverse $ init cls)
    if length opCls + length scCls < length cls - 2 -- check the operation clauses
      then throwError "Unknown or unordered clauses"
      else return ()
    let sclist = map (\(ScClause l _ _ _ _) -> l) scCls
    let hsc    = \name ->
          do ScClause _ x p k c <- find (\(ScClause l _ _ _ _) -> l == name) scCls
             return (x, p, k, c)
    return $ Handler hname tyopt oplist sclist hreturn hop hsc hfwd
  where
    isOp x = case x of
              OpClause {} -> True
              _ -> False
    isSc x = case x of
              ScClause {} -> True
              _ -> False

----------------------------------------------------------------
-- | Memory datatype
newtype Memory s = Mem { runMem :: Name -> Maybe s }
instance Eq (Memory a) where
  x == y = True

instance Show (Memory s) where
  show _ = "<memory>"
instance Functor Memory where
  fmap f (Mem m) = Mem (fmap (fmap f) m)

emptymem :: Memory s
emptymem = Mem $ const Nothing
retrieve :: Name -> Memory s -> s
retrieve x m = case runMem m x of Just s  -> s
                                  Nothing -> error "var undefined"
update :: (Name, s) -> Memory s -> Memory s
update (x, s) m = Mem $ \ y -> if x == y then Just s else runMem m y