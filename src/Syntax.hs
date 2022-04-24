{-# LANGUAGE FlexibleContexts #-}

module Syntax where

import Control.Monad.Except

type Err = String
type Name = String

-- | Value syntax
data Value 
  = Var Name Int  -- ^ use De Bruijn Index
  | Lam Name Comp
  | Vunit
  | Vpair (Value, Value)
  | Vhandler Handler
  -- Vhandler Handler
  -- extensions:
  | Vbool Bool
  | Vint Int
  | Vchar Char
  | Vstr String   -- ^ for simplicity, we separate lists and strings
  | Vlist [Value]
  | Vsum (Either Value Value)
  | Vret Value | Vflag Value
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

-- 在这里检查语句的种类和数量
clauses2handler :: MonadError Err m => [Clause] -> m Handler
clauses2handler cls = return Handler { hname = show cls
                                     , oplist = []
                                     , sclist = []
                                     , hreturn = undefined
                                     , hop = undefined
                                     , hsc = undefined
                                     , hfwd = undefined
                                     }

infixr 0 :.
data (Dot a b) = a :. b deriving (Show, Eq)

-- | Computation syntax
data Comp
  = Return Value                                   -- ^ return v
  | Op Name Value (Dot Name Comp)                  -- ^ op l v (y.c)
  | Sc Name Value (Dot Name Comp) (Dot Name Comp)  -- ^ sc l v (y.c1) (z.c2)
  | Handle Handler Comp                            -- ^ v ★ c
  | Do Name Comp Comp                              -- ^ do x <- c1 in c2
  | App Value Value                                -- ^ v1 v2
  | Let Name Value Comp                            -- ^ let x = v in c
  -- extensions:
  -- We implement most functions in the paper as built-in functions
  -- because the interpreter doesn't support pattern matching and recursive functions.
  | If Value Comp Comp
  | Case Value Name Comp Name Comp
  | Eq Value Value
  | Larger Value Value
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
  deriving (Show, Eq)

infixr 8 #
(#) :: Handler -> Comp -> Comp
h # c = Handle h c

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