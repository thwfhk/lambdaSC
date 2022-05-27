{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

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
  , oplist  :: [Name]                                 -- ^ algberaic operations names
  , sclist  :: [Name]                                 -- ^ scoped operations names
  , hreturn :: (Name, Comp)                           -- ^ (x, c)
  , hop     :: Name -> Maybe (Name, Name, Comp)       -- ^ l -> (x, k, c)
  , hsc     :: Name -> Maybe (Name, Name, Name, Comp) -- ^ l -> (x, p, k, c)
  , hfwd    :: (Name, Name, Name, Comp)               -- ^ (f, p, k, c)
  }
instance Show Handler where
  show (Handler name _ _ _ _ _ _) = "handler{" ++ name ++ "}"

instance Eq Handler where
  Handler x _ _ _ _ _ _ == Handler y _ _ _ _ _ _ = x == y

infixr 0 :.
data (Dot a b) = a :. b deriving (Show, Eq)

-- | Computation syntax
data Comp
  = Return Value                                   -- ^ return v
  | Op Name Value (Dot Name Comp)                  -- ^ op l v (y.c)
  | Sc Name Value (Dot Name Comp) (Dot Name Comp)  -- ^ sc l v (y.c1) (z.c2)
  | Handle Value Comp                            -- ^ v ★ c
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

-- value type
data VType
  = TVar Name
  | TArr VType CType
  | TUnit
  | TPair VType VType
  | THand CType CType
  | TBool
  | TInt
  | TEmpty
  deriving (Show, Eq)

data CType = CT VType EType
  deriving (Show, Eq)

data EType
  = EVar Name
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

----------------------------------------------------------------
-- Free type variables and their kinds

class FreeVars a where
  freeVars :: a -> S.Set (Name, Kind)

instance FreeVars VType where
  freeVars (TVar x) = S.singleton (x, ValueType)
  freeVars (TArr t1 t2) = freeVars t1 `S.union` freeVars t2
  freeVars (TPair t1 t2) = freeVars t1 `S.union` freeVars t2
  freeVars (THand t1 t2) = freeVars t1 `S.union` freeVars t2
  freeVars _ = S.empty

instance FreeVars SType where
  freeVars (Mono t) = freeVars t
  freeVars (Forall x k t) = S.delete (x, k) (freeVars t)

instance FreeVars CType where
  freeVars (CT t1 t2) = freeVars t1 `S.union` freeVars t2

instance FreeVars EType where
  freeVars (EVar x) = S.singleton (x, EffectType)
  freeVars (ECons _ t2) = freeVars t2
  freeVars EEmpty = S.empty

instance FreeVars Type where
  freeVars (Left t) = freeVars t
  freeVars (Right t) = freeVars t

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


----------------------------------------------------------------
-- Utilities

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
clauses2handler :: MonadError Err m => [Clause] -> m Handler
clauses2handler cls = do
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
    return $ Handler hname oplist sclist hreturn hop hsc hfwd
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