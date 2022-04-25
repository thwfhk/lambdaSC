module Examples where

import Syntax
import Evaluation
import Prelude hiding ((<>))


----------------------------------------------------------------

-- | The @lift@ syntactic sugar
lift2fwd :: (Name, Name, Comp) -> (Name, Name, Name, Comp)
lift2fwd (k, z, c) = ( "f", "p", "k",
  App (Var "f" 2) $ Vpair (Var "p" 1, Lam "z" c ))

----------------------------------------------------------------
-- * Some Auxiliary Functions :

-- | @app2 f v1 v2@ applies the function @f@ to two arguments @v1@ and @v2@.
app2 :: Value -> Value -> Value -> Comp
app2 f v1 v2 = Do "f'" (App f v1) $ App (Var "f'" 0) (shiftV 1 v2)

-- | Generic Algebraic Operation.
op :: Name -> Value -> Comp
op l x = Op l x ("y" :. Return (Var "y" 0))

-- | Generic Scoped Operation.
sc :: Name -> Value -> Dot Name Comp -> Comp
sc l x p = Sc l x p ("z" :. Return (Var "z" 0))

-- | @absurd@ is only used for well-typedness. We can omit it for now.
absurd :: Value -> Comp
absurd x = undefined

----------------------------------------------------------------
-- * Section 2.1 & Section 5: Inc

-- | @hInc@ refers to the @h_inc@ handler in Section 2.1 and Section 5
hInc :: Value
hInc = Vhandler $ Handler
  "hInc" ["inc"] []
  ("x", Return . Lam "s" $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "inc" -> Just ("_", "k",
      Return . Lam "s" $ Do "k'" (App (Var "k" 1) (Var "s" 0)) $
                         Do "s'" (Add (Var "s" 1) (Vint 1)) $
                         App (Var "k'" 1) (Var "s'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Fst (Var "zs" 0)) $
                 Do "s'" (Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- | @runInc@ is a macro to help applying the initial count value
runInc :: Int -> Comp -> Comp
runInc s c = Do "c'" (hInc # c) $ App (Var "c'" 0) (Vint s)

-- | @cInc@ refers to the @c_inc@ program in Section 2.1
cInc :: Comp
cInc = Op "choose" Vunit ("b" :.
        If (Var "b" 0) (op "inc" Vunit) (op "inc" Vunit))

-- Handling @cInc@:
-- >>> eval $ hOnce # runInc 0 cInc
-- >>> eval $ runInc 0 (hOnce # cInc)
-- Return (Vlist [Vpair (Vint 0,Vint 1),Vpair (Vint 0,Vint 1)])
-- Return (Vpair (Vlist [Vint 0,Vint 1],Vint 2))

cFwd :: Comp
cFwd = Sc "once" Vunit ("_" :. cInc) ("x" :. Op "inc" Vunit ("y" :. 
        Do "z" (Add (Var "x" 1) (Var "y" 0)) $ Return (Var "z" 0)))

-- Handling @cFwd@:
-- >>> eval $ hOnce # runInc 0 cFwd
-- Return (Vlist [Vpair (Vint 1,Vint 2)])

----------------------------------------------------------------
-- * Section 2.2 & Section 7.1 : Nondeterminism with Once

-- | @hOnce@ refers to the @h_once@ handler in Section 2.2 & Section 7.1
hOnce :: Value
hOnce = Vhandler $ Handler
  "hOnce" ["choose", "fail"] ["once"]
  ("x", Return $ Vlist [Var "x" 0])
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return $ Vlist [])
    "choose" -> Just ("x", "k",
      Do "xs" (App (Var "k" 0) (Vbool True)) $
      Do "ys" (App (Var "k" 1) (Vbool False)) $
      Append (Var "xs" 1) (Var "ys" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "once" -> Just ("_", "p", "k",
      Do "ts" (App (Var "p" 1) Vunit) $
      Do "t" (Head (Var "ts" 0)) $
      App (Var "k" 2) (Var "t" 0))
    _ -> Nothing)
  (lift2fwd ("k", "z", ConcatMap (Var "z" 0) (Var "k" 1)))

-- | @failure@ is a wrapper for @fail@ with a polymorphic return type.
-- Defined in Section 7.1
failure :: Comp
failure = Op "fail" Vunit ("y" :. absurd (Var "y" 0))

-- | @cOnce@ refers to the @c_once@ program in Section 2.3
cOnce :: Comp
cOnce = Sc "once" Vunit ("_" :. op "choose" Vunit)
                        ("b" :. If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails")))

-- Handling @cOnce@:
-- >>> eval $ hOnce # cOnce
-- Return (Vlist [Vstr "heads"])

----------------------------------------------------------------
-- * Section 7.2 : Nondeterminism with Cut

-- | @hCut@ refers to the @h_cut@ handler in Section 7.2
hCut :: Value
hCut = Vhandler $ Handler
  "hCut" ["choose", "fail", "cut"] ["call"]
  ("x", Return . Vret $ Vlist [Var "x" 0])
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return . Vret $ Vlist [])
    "choose" -> Just ("x", "k",
      Do "xs" (App (Var "k" 0) (Vbool True)) $
      Do "ys" (App (Var "k" 1) (Vbool False)) $
      AppendCut (Var "xs" 1) (Var "ys" 0))
    "cut" -> Just ("_", "k", Do "x" (App (Var "k" 0) Vunit) $ Close (Var "x" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "call" -> Just ("_", "p", "k",
      Do "x" (App (Var "p" 1) Vunit) $
      Do "x'" (Open (Var "x" 0)) $
      ConcatMapCutList (Var "x'" 0) (Var "k" 2))
    _ -> Nothing)
  (lift2fwd ("k", "z", ConcatMapCutList (Var "z" 0) (Var "k" 1)))

-- | A simple program simulates the behavior of @cOnce@ using @cut@ and @call@.
cCut :: Comp
cCut = Do "b" (sc "call" Vunit ("_" :.
          Do "y" (op "choose" Vunit) $
          If (Var "y" 0) (Do "_" (op "cut" Vunit) $ Return (Vbool True))
                         (Return (Vbool False)))) $
       If (Var "b" 0) (Return (Vstr "heads")) (Return (Vstr "tails"))

-- Handling @cCut@:
-- >>> eval $ hCut # cCut
-- Return (Vret (Vlist [Vstr "heads"]))


----------------------------------------------------------------
-- * Section 7.3 : Exceptions

-- | @hExcept@ refers to the @h_except@ handler in Section 7.3
hExcept :: Handler
hExcept = Handler
  "hExcept" ["raise"] ["catch"]
  ("x", Return $ Vsum (Right (Var "x" 0)))
  (\ oplabel -> case oplabel of
    "raise" -> Just ("e", "_", Return $ Vsum (Left (Var "e" 1)))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "catch" -> Just ("e", "p", "k",
      Do "x" (App (Var "p" 1) (Vbool True)) $
      -- NOTE: A little different from the paper.
      -- We assume Eq is defined for |String + alpha| for simplicity.
      Do "b" (Eq (Var "x" 0) (Vsum (Left (Var "e" 3)))) $
      If (Var "b" 0)
        (Do "y" (App (Var "p" 3) (Vbool False)) $ app2 exceptMap (Var "y" 0) (Var "k" 3))
        (app2 exceptMap (Var "x" 1) (Var "k" 2)))
    _ -> Nothing)
  (lift2fwd ("k", "z", app2 exceptMap (Var "z" 0) (Var "k" 1)))

-- | @exceptMap@ refers to the @exceptMap@ function in Section 7.3
exceptMap :: Value
exceptMap = Lam "z" . Return . Lam "k" $
  Case (Var "z" 1) "e" (Return (Vsum (Left (Var "e" 0))))
                   "x" (App (Var "k" 1) (Var "x" 0))

-- | @cRaise@ refers to the @_raise@ program in Section 7.3
cRaise :: Comp
cRaise = Do "x" (op "inc" Vunit) $
         Do "b" (Larger (Var "x" 0) (Vint 10)) $
         If (Var "b" 0) (Op "raise" (Vstr "Overflow") ("y" :. absurd (Var "y" 0)))
                        (Return (Var "x" 0))

-- | @cCatch@ refers to the @c_catch@ program in Section 7.3
cCatch :: Comp
cCatch = sc "catch" (Vstr "Overflow") ("b" :. If (Var "b" 0) cRaise (Return (Vint 10)))

-- Handling @cCatch@:
-- >>> eval $ hExcept # runInc 42 cCatch
-- >>> eval $ runInc 42 (hExcept # cCatch)
-- Return (Vsum (Right (Vpair (Vint 10,Vint 42))))
-- Return (Vpair (Vsum (Right (Vint 10)),Vint 43))

----------------------------------------------------------------
-- * Section 7.4 : Local State

-- | @hState@ refers to the @h_state@ handler in Section 7.4
hState :: Value
hState = Vhandler $ Handler
  "hState" ["get", "put"] ["local"]
  ("x", Return . Lam "m" $ Return (Vpair (Var "x" 1, Var "m" 0)))
  (\ oplabel -> case oplabel of
    "get" -> Just ("x", "k",
      Return . Lam "m" $ Do "v" (Retrieve (Var "x" 2) (Var "m" 0)) $
                         Do "k'" (App (Var "k" 2) (Var "v" 0)) $
                         App (Var "k'" 0) (Var "m" 2))
    "put" -> Just ("pa", "k",
      Return . Lam "m" $ Do "k'" (App (Var "k" 1) Vunit) $
                         Do "m'" (Update (Var "pa" 3) (Var "m" 1)) $
                         App (Var "k'" 1) (Var "m'" 0))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "local" -> Just ("xv", "p", "k",
      Return . Lam "m" $ Do "x" (Fst (Var "xv" 3)) $
                         Do "v" (Snd (Var "xv" 4)) $
                         Do "um" (Update (Var "xv" 5) (Var "m" 2)) $
                         Do "p'" (App (Var "p" 5) Vunit) $
                         Do "tm" (App (Var "p'" 0) (Var "um" 1)) $
                         Do "t" (Fst (Var "tm" 0)) $
                         Do "m'" (Snd (Var "tm" 1)) $
                         Do "k'" (App (Var "k" 8) (Var "t" 1)) $
                         Do "oldv" (Retrieve (Var "x" 7) (Var "m" 8)) $
                         Do "newm" (Update (Vpair (Var "x" 8, Var "oldv" 0)) (Var "m'" 2)) $
                         App (Var "k'" 2) (Var "newm" 0))
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Fst (Var "zs" 0)) $
                 Do "s'" (Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- | @cState@ refers to the @c_state@ program in Section 7.4
cState :: Comp
cState = Do "_" (op "put" (Vpair (Vstr "x", Vint 10))) $
         Do "x1" (sc "local" (Vpair (Vstr "x", Vint 42)) ("_" :. op "get" (Vstr "x"))) $
         Do "x2" (op "get" (Vstr "x")) $
         Return (Vpair (Var "x1" 1, Var "x2" 0))

-- Handling @cState@:
handle_cState :: Comp
handle_cState = Do "m" (Newmem Vunit) $ 
                Do "c" (hState # cState) $
                Do "x" (App (Var "c" 0) (Var "m" 1)) $
                Fst (Var "x" 0)
-- >>> eval handle_cState
-- Return (Vpair (Vint 42,Vint 10))

----------------------------------------------------------------
-- * Section 7.5 : Depth-Bounded Search

-- | @hDepth@ refers to the @h_depth@ handler in Section 7.5
hDepth :: Value
hDepth = Vhandler $ Handler
  "hDepth" ["choose", "fail"] ["depth"]
  ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose"   -> Just ("x", "k", Return . Lam "d" $
      Do "b" (Eq (Var "d" 0) (Vint 0)) $
      If (Var "b" 0) (Return (Vlist []))
                     (Do "k1" (App (Var "k" 2) (Vbool True)) $
                      Do "k2" (App (Var "k" 3) (Vbool False)) $
                      Do "d'" (Add (Var "d" 3) (Vint (-1))) $
                      Do "xs" (App (Var "k1" 2) (Var "d'" 0)) $
                      Do "ys" (App (Var "k2" 2) (Var "d'" 1)) $
                      Append (Var "xs" 1) (Var "ys" 0) ))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . Lam "d" $
      Do "p'" (App (Var "p" 2) Vunit) $
      Do "xs" (App (Var "p'" 0) (Var "d'" 4)) $
      ConcatMap (Var "xs" 0) (Lam "v_" $ Do "v" (Fst (Var "v_" 0)) $
                                         Do "k'" (App (Var "k" 5) (Var "v" 0)) $
                                         App (Var "k'" 0) (Var "d" 5)))
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "d" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "d" 2)
    , Lam "vs" $ ConcatMap (Var "vs" 0) (Lam "vd" $
        Do "v" (Fst (Var "vd" 0)) $
        Do "d" (Snd (Var "vd" 1)) $
        Do "k'" (App (Var "k" 5) (Var "v" 1)) $
        App (Var "k'" 0) (Var "d" 1))
    )))

-- | @hDepth2@ is another handler for @depth@.
-- The depth consumed by the scoped computation is also counted in the global depth bound.
hDepth2 :: Value
hDepth2 = Vhandler $ Handler
  "hDepth" ["choose", "fail"] ["depth"]
  ("x", Return . Lam "d" $ Return (Vlist [Vpair (Var "x" 1, Var "d" 0)]))
  (\ oplabel -> case oplabel of
    "fail" -> Just ("_", "_", Return (Vlist []))
    "choose"   -> Just ("x", "k", Return . Lam "d" $
      Do "b" (Eq (Var "d" 0) (Vint 0)) $
      If (Var "b" 0) (Return (Vlist []))
                     (Do "k1" (App (Var "k" 2) (Vbool True)) $
                      Do "k2" (App (Var "k" 3) (Vbool False)) $
                      Do "d'" (Add (Var "d" 3) (Vint (-1))) $
                      Do "xs" (App (Var "k1" 2) (Var "d'" 0)) $
                      Do "ys" (App (Var "k2" 2) (Var "d'" 1)) $
                      Append (Var "xs" 1) (Var "ys" 0) ))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    "depth" -> Just ("d'", "p", "k", Return . Lam "d" $
      Do "p'" (App (Var "p" 2) Vunit) $
      Do "md" (Min (Var "d'" 4) (Var "d" 1)) $
      Do "xs" (App (Var "p'" 1) (Var "md" 0)) $
      ConcatMap (Var "xs" 0) (Lam "vd" $ Do "v" (Fst (Var "vd" 0)) $
                                         Do "rd" (Snd (Var "vd" 1)) $
                                         Do "consumed" (Minus (Var "md" 4) (Var "rd" 0)) $
                                         Do "trued" (Minus (Var "d" 7) (Var "consumed" 0)) $
                                         Do "k'" (App (Var "k" 9) (Var "v" 3)) $
                                         App (Var "k'" 0) (Var "trued" 1)))
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "d" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "d" 2)
    , Lam "vs" $ ConcatMap (Var "vs" 0) (Lam "vd" $
        Do "v" (Fst (Var "vd" 0)) $
        Do "d" (Snd (Var "vd" 1)) $
        Do "k'" (App (Var "k" 5) (Var "v" 1)) $
        App (Var "k'" 0) (Var "d" 1))
    )))

-- | @cDepth@ refers to the @c_depth@ program in Section 7.5
cDepth :: Comp
cDepth = Sc "depth" (Vint 1) ("_" :.
 Do "b" (op "choose" Vunit) $
 If (Var "b" 0) (Return (Vint 1))
                ( Do "b'" (op "choose" Vunit) $
                  If (Var "b'" 0)
                     (Return (Vint 2))
                     (Return (Vint 3))))
  ("x" :.
   Do "b" (op "choose" Vunit) $
   If (Var "b" 0) (Return (Var "x" 1))
                  ( Do "b'" (op "choose" Vunit) $
                    If (Var "b'" 0)
                       (Return (Vint 4))
                       (Do "b''" (op "choose" Vunit) $
                         If (Var "b''" 0)
                            (Return (Vint 5))
                            (Return (Vint 6)))))

-- Handling @cDepth@:
-- >>> eval $ Do "f" (hDepth # cDepth) $ App (Var "f" 0) (Vint 2)
-- >>> eval $ Do "f" (hDepth2 # cDepth) $ App (Var "f" 0) (Vint 2)
-- Return (Vlist [Vpair (Vint 1,Vint 1),Vpair (Vint 4,Vint 0)])
-- Return (Vlist [Vpair (Vint 1,Vint 0)])

----------------------------------------------------------------
-- * Section 7.6 : Parsers

-- | @hToken@ refers to the @h_token@ handler in Section 7.6
hToken :: Value
hToken = Vhandler $ Handler
  "hToken" ["token"] []
  ("x", Return . Lam "s" $ Return (Vpair (Var "x" 1, Var "s" 0)))
  (\ oplabel -> case oplabel of
    "token" -> Just ("x", "k", Return . Lam "s" $
      Do "b" (Eq (Var "s" 0) (Vstr "")) $
      If (Var "b" 0) failure
                     ( Do "x'" (HeadS (Var "s" 1)) $
                       Do "xs" (TailS (Var "s" 2)) $
                       Do "b" (Eq (Var "x" 5) (Var "x'" 1)) $
                       If (Var "b" 0) (app2 (Var "k" 5) (Var "x" 6) (Var "xs" 1)) failure))
    _ -> Nothing)
  (\ sclabel -> case sclabel of
    _ -> Nothing)
  ("f", "p", "k", Return . Lam "s" $ App (Var "f" 3) (Vpair
    ( Lam "y" $ Do "p'" (App (Var "p" 3) (Var "y" 0)) $
                App (Var "p'" 0) (Var "s" 2)
    , Lam "zs" $ Do "z" (Fst (Var "zs" 0)) $
                 Do "s'" (Snd (Var "zs" 1)) $
                 Do "k'" (App (Var "k" 4) (Var "z" 1)) $
                 App (Var "k'" 0) (Var "s'" 1)
    )))

-- | @<>@ refers to the syntactic sugar @<>@ in Section 7.6
(<>) :: Comp -> Comp -> Comp
x <> y = Op "choose" Vunit ("b" :. If (Var "b" 0) (shiftC 1 x) (shiftC 1 y))

-- Parsers defined in Fig. 7 :
digit :: Value
digit =  Lam "_" $ 
         op "token" (Vchar '0')
      <> op "token" (Vchar '1')
      <> op "token" (Vchar '2')
      <> op "token" (Vchar '3')
      <> op "token" (Vchar '4')
      <> op "token" (Vchar '5')
      <> op "token" (Vchar '6')
      <> op "token" (Vchar '7')
      <> op "token" (Vchar '8')
      <> op "token" (Vchar '9')
-- | For simplicity, we directly use Haskell's recursion to implement the recursive function @many1@.
many1 :: Value -> Comp
many1 p = Do "a" (App p Vunit) $
          Do "as" (many1 p <> Return (Vstr "")) $
          Do "x" (ConsS (Var "a" 1) (Var "as" 0)) $
          Return (Var "x" 0)
expr :: Value
expr = Lam "_" $
       (Do "i" (App term Vunit) $
        Do "_" (op "token" (Vchar '+')) $
        Do "j" (App expr Vunit) $
        Do "x" (Add (Var "i" 2) (Var "j" 0)) $
        Return (Var "x" 0))
    <> (Do "i" (App term Vunit) $ Return (Var "i" 0))
term :: Value
term = Lam "_" $
       (Do "i" (App factor Vunit) $
        Do "_" (op "token" (Vchar '*')) $
        Do "j" (App term Vunit) $
        Do "x" (Mul (Var "i" 2) (Var "j" 0)) $
        Return (Var "x" 0))
    <> (Do "i" (App factor Vunit) $ Return (Var "i" 0))
factor :: Value
factor = Lam "_" $
         (Do "ds" (many1 digit) $
          Do "x" (Read (Var "ds" 0)) $
          Return (Var "x" 0))
      <> (Do "_" (op "token" (Vchar '(')) $
          Do "i" (App expr Vunit) $
          Do "_" (op "token" (Vchar ')')) $
          Return (Var "i" 1))

-- | @expr1@ refers to the @expr_1@ parser in Section 7.6
expr1 :: Value
expr1 = Lam "_" $
        Do "i" (App term Vunit) $
        sc "call" Vunit ("_" :. ( Do "_" (op "token" (Vchar '+')) $
                                  Do "_" (op "cut" Vunit) $
                                  Do "j" (App expr1 Vunit) $
                                  Do "x" (Add (Var "i" 4) (Var "j" 0)) $
                                  Return (Var "x" 0)) <> Return (Var "i" 1))


-- Handling @expr1@:
handle_expr1 :: Comp
handle_expr1 = hCut # (Do "c" (hToken # App expr1 Vunit) $
                       App (Var "c" 0) (Vstr "(2+5)*8"))
-- >>> eval $ handle_expr1
-- Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")]))

-- Handling @expr@:
handle_expr :: Comp
handle_expr = hCut # (Do "c" (hToken # App expr Vunit) $
                      App (Var "c" 0) (Vstr "(2+5)*8"))
-- >>> eval $ handle_expr
-- Return (Vret (Vlist [Vpair (Vint 56,Vstr ""),Vpair (Vint 7,Vstr "*8")]))
