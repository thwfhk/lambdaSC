module Evaluation where

import Syntax
import Debug.Trace


-- | Evaluation
eval :: Comp -> Comp
eval c = case eval1 c of
  Just c' -> eval c'
  Nothing -> c

-- | Single step evaluation
eval1 :: Comp -> Maybe Comp
eval1 (App (Lam x c) v) = return . shiftC (-1) $ subst c [(shiftV 1 v, 0)]

eval1 (Let x v c) = return . shiftC (-1) $ subst c [(shiftV 1 v, 0)]

eval1 (Do x (Return v) c) = return . shiftC (-1) $ subst c [(shiftV 1 v, 0)]
eval1 (Do x (Op l v (y :. c1)) c2) = return $ Op l v (y :. Do x c1 c2)
eval1 (Do x (Sc l v (y :. c1) (z :. c2)) c3) = return $ Sc l v (y :. c1) (z :. Do x c2 c3)
eval1 (Do x c1 c2) = do c1' <- eval1 c1; return $ Do x c1' c2

eval1 (Handle h@(Vhandler h') (Return v)) = return $ let (x, cr) = hreturn h' in
  shiftC (-1) $ subst cr [(shiftV 1 v, 0)]
eval1 (Handle h@(Vhandler h') (Op l v (y :. c1))) = return $ case hop h' l of
  Just (x, k, c) -> shiftC (-2) $ subst c [ (shiftV 2 v, 1)
                                          , (shiftV 2 $ Lam y (Handle h c1), 0) ]
  Nothing -> Op l v (y :. Handle h c1)
eval1 (Handle h@(Vhandler h') (Sc l v (y :. c1) (z :. c2))) = return $ case hsc h' l of
  Just (x, p, k, c) -> shiftC (-3) $ subst c [ (shiftV 3 v, 2)
                                             , (shiftV 3 $ Lam y (Handle h c1), 1)
                                             , (shiftV 3 $ Lam z (Handle h c2), 0) ]
  Nothing -> case hfwd h' of
    (f, p, k, c) -> shiftC (-3) $ subst c
      [ (shiftV 3 $ Lam y (Handle h c1), 1)
      , (shiftV 3 $ Lam z (Handle h c2), 0)
      , (Lam "pk" $ 
          Do "p" (Fst (Var "pk" 0)) $
          Do "k" (Snd (Var "pk" 1)) $
          Sc l (shiftV 3 v) (y :. App (Var p 2) (Var y 0)) (z :. App (Var k 1) (Var z 0)), 2)
      ]
eval1 (Handle h c) = do c' <- eval1 c; return $ Handle h c'

-- extensions:
eval1 (If (Vbool b) c1 c2) = return $ if b then c1 else c2
eval1 (Eq v1 v2) = return $ if v1 == v2 then Return (Vbool True) else Return (Vbool False)
eval1 (Larger (Vint x) (Vint y)) = return $ if x > y then Return (Vbool True) else Return (Vbool False)
eval1 (Case (Vsum v) x c1 y c2) = return $ case v of
  Left t  -> shiftC (-1) $ subst c1 [(shiftV 1 t, 0)]
  Right t -> shiftC (-1) $ subst c2 [(shiftV 1 t, 0)]
eval1 (Add (Vint x) (Vint y)) = return . Return . Vint $ x + y
eval1 (Minus (Vint x) (Vint y)) = return . Return . Vint $ x - y
eval1 (Min (Vint x) (Vint y)) = return . Return . Vint $ min x y
eval1 (Mul (Vint x) (Vint y)) = return . Return . Vint $ x * y
eval1 (Fst (Vpair (x, y))) = return . Return $ x
eval1 (Snd (Vpair (x, y))) = return . Return $ y

eval1 (Append (Vlist xs) (Vlist ys)) = return . Return . Vlist $ xs ++ ys
eval1 (Head (Vlist xs)) = return . Return . head $ xs
eval1 (Tail (Vlist xs)) = return . Return . Vlist . tail $ xs
eval1 (ConcatMap (Vlist xs) f) = return $ case xs of
  [] -> Return . Vlist $ []
  (x:xs) -> Do "as" (App f x) $
            Do "as'" (ConcatMap (shiftV 1 $ Vlist xs) (shiftV 1 f)) $
            Append (Var "as" 1) (Var "as'" 0)

eval1 (AppendS (Vstr xs) (Vstr ys)) = return . Return . Vstr $ xs ++ ys
eval1 (HeadS (Vstr xs)) = return . Return . Vchar . head $ xs
eval1 (TailS (Vstr xs)) = return . Return . Vstr . tail $ xs
eval1 (ConsS (Vchar x) (Vstr xs)) = return . Return . Vstr $ (x:xs)
eval1 (Read (Vstr xs)) = return . Return . Vint $ read xs

eval1 (Retrieve (Vstr name) (Vmem m)) = return . Return $ retrieve name m
eval1 (Update (Vpair (Vstr x, v)) (Vmem m)) = return . Return $ Vmem (update (x, v) m)
eval1 (Newmem Vunit) = return . Return $ Vmem emptymem

eval1 (AppendCut (Vret (Vlist xs)) (Vret (Vlist ys)))  = return . Return . Vret  . Vlist $ xs ++ ys
eval1 (AppendCut (Vret (Vlist xs)) (Vflag (Vlist ys))) = return . Return . Vflag . Vlist $ xs ++ ys
eval1 (AppendCut (Vflag (Vlist xs)) _)                 = return . Return . Vflag . Vlist $ xs
eval1 (ConcatMapCutList (Vret (Vlist xs)) f) = return $ case xs of
  [] -> Return . Vret . Vlist $ []
  (x:xs) -> Do "as" (App f x) $
            Do "as'" (ConcatMapCutList (shiftV 1 $ Vret (Vlist xs)) (shiftV 1 f)) $
            AppendCut (Var "as" 1) (Var "as'" 0)
eval1 (ConcatMapCutList (Vflag (Vlist xs)) f) = return $ case xs of
  [] -> Return . Vflag . Vlist $ []
  (x:xs) -> Do "as" (App f x) $
            Do "as'" (ConcatMapCutList (shiftV 1 $ Vflag (Vlist xs)) (shiftV 1 f)) $
            AppendCut (Var "as" 1) (Var "as'" 0)
eval1 (Close (Vret (Vlist xs)))  = return . Return . Vflag . Vlist $ xs
eval1 (Close (Vflag (Vlist xs))) = return . Return . Vflag . Vlist $ xs
eval1 (Open  (Vret (Vlist xs)))  = return . Return . Vret  . Vlist $ xs
eval1 (Open  (Vflag (Vlist xs))) = return . Return . Vret  . Vlist $ xs

eval1 c = Nothing

----------------------------------------------------------------

-- | The @lift@ syntactic sugar
lift2fwd :: (Name, Name, Comp) -> (Name, Name, Name, Comp)
lift2fwd (k, z, c) = ( "f", "p", "k",
  App (Var "f" 2) $ Vpair (Var "p" 1, Lam "z" c ))

----------------------------------------------------------------
-- Auxiliary functions for implementing the evaluation:

mapC :: (Comp -> Comp) -> (Value -> Value) -> (Comp -> Comp)
mapC fc fv c = case c of
  Return v -> Return (fv v)
  Op l v (y :. c) -> Op l (fv v) (y :. fc c)
  Sc l v (y :. c1) (z :. c2) -> Sc l (fv v) (y :. fc c1) (z :. fc c2)
  Handle v c -> Handle (fv v) (fc c)
  Do x c1 c2 -> Do x (fc c1) (fc c2)
  App v1 v2 -> App (fv v1) (fv v2)
  Let x v c  -> Let x (fv v) (fc c)
  If v c1 c2 -> If (fv v) (fc c1) (fc c2)
  Case v x c1 y c2 -> Case (fv v) x (fc c1) y (fc c2)
  Eq v1 v2 -> Eq (fv v1) (fv v2)
  Larger v1 v2 -> Larger (fv v1) (fv v2)
  Add v1 v2 -> Add (fv v1) (fv v2)
  Minus v1 v2 -> Minus (fv v1) (fv v2)
  Min v1 v2 -> Min (fv v1) (fv v2)
  Mul v1 v2 -> Mul (fv v1) (fv v2)
  Append v1 v2 -> Append (fv v1) (fv v2)
  Head v -> Head (fv v)
  Tail v -> Tail (fv v)
  Fst v -> Fst (fv v)
  Snd v -> Snd (fv v)
  AppendS v1 v2 -> AppendS (fv v1) (fv v2)
  HeadS v -> HeadS (fv v)
  TailS v -> TailS (fv v)
  ConsS v1 v2 -> ConsS (fv v1) (fv v2)
  Read v -> Read (fv v)
  AppendCut v1 v2 -> AppendCut (fv v1) (fv v2)
  ConcatMap v1 v2 -> ConcatMap (fv v1) (fv v2)
  Retrieve v1 v2 -> Retrieve (fv v1) (fv v2)
  Update v1 v2 -> Update (fv v1) (fv v2)
  ConcatMapCutList v1 v2 -> ConcatMapCutList (fv v1) (fv v2)
  Close v -> Close (fv v)
  Open v -> Open (fv v)
  Newmem v -> Newmem (fv v)
  -- oth -> oth

mapH :: (Comp -> Comp) -> Handler -> Handler
mapH fc h = h { hreturn = hr, hop = ho, hsc = hs, hfwd = hf }
  where
    hr = let (x, c) = hreturn h in (x, fc c)
    ho l = hop h l >>= \ (x, k, c) -> return (x, k, fc c)
    hs l = hsc h l >>= \ (x, p, k, c) -> return (x, p, k, fc c)
    hf = let (f, p, k, c) = hfwd h in (f, p, k, fc c)

mapV :: (Comp -> Comp) -> (Value -> Value) -> Value -> Value
mapV fc fv v = case v of
  Var x n -> Var x n
  Lam x c -> Lam x (fc c)
  Vpair (v1, v2) -> Vpair (fv v1, fv v2)
  Vsum v -> case v of
    Left t -> Vsum (Left (fv t))
    Right t -> Vsum (Right (fv t))
  Vlist xs -> Vlist (fmap fv xs)
  Vmem m -> Vmem (fmap fv m)
  Vret v -> Vret (fv v)
  Vflag v -> Vflag (fv v)
  Vunit -> Vunit
  Vbool b -> Vbool b
  Vint n -> Vint n
  Vstr s -> Vstr s
  Vchar c -> Vchar c
  Vhandler h -> Vhandler (mapH fc h)
  -- oth -> oth

varmapC :: (Int -> (Name, Int) -> Value) -> Int -> Comp -> Comp
varmapC onvar cur c = case c of
    Op l v (y :. c) -> Op l (fv cur v) (y :. fc (cur+1) c)
    Sc l v (y :. c1) (z :. c2) -> Sc l (fv cur v) (y :. fc (cur+1) c1) (z :. fc (cur+1) c2)
    Handle v c -> Handle (fv cur v) (fc cur c)
    Do x c1 c2 -> Do x (fc cur c1) (fc (cur+1) c2)
    Let x v c  -> Let x (fv cur v) (fc (cur+1) c)
    Case v x c1 y c2 -> Case (fv cur v) x (fc (cur+1) c1) y (fc (cur+1) c2)
    oth -> mapC (fc cur) (fv cur) oth
  where
    fc = varmapC onvar
    fv = varmapV onvar

varmapH :: (Int -> (Name, Int) -> Value) -> Int -> Handler -> Handler
varmapH onvar cur h = h { hreturn = hr, hop = ho, hsc = hs, hfwd = hf }
  where
    hr = let (x, c) = hreturn h in (x, fc (cur+1) c)
    ho l = hop h l >>= \ (x, k, c) -> return (x, k, fc (cur+2) c)
    hs l = hsc h l >>= \ (x, p, k, c) -> return (x, p, k, fc (cur+3) c)
    hf = let (f, p, k, c) = hfwd h in (f, p, k, fc (cur+4) c)
    fc = varmapC onvar
    fv = varmapV onvar

varmapV :: (Int -> (Name, Int) -> Value) -> Int -> Value -> Value
varmapV onvar cur v = case v of
    Var x i -> onvar cur (x, i)
    Lam x c -> Lam x (fc (cur+1) c)
    oth -> mapV (fc cur) (fv cur) oth
  where
    fc = varmapC onvar
    fv = varmapV onvar

shiftV :: Int -> Value -> Value
shiftV delta v = varmapV (\ cur (x, i) -> if i >= cur then Var x (i+delta) else Var x i) 0 v

shiftC :: Int -> Comp -> Comp
shiftC delta v = varmapC (\ cur (x, i) -> if i >= cur then Var x (i+delta) else Var x i) 0 v

substC :: Comp -> (Value, Int) -> Comp
substC c (v, j) = varmapC (\ cur (x, i) -> if i == j+cur then shiftV cur v else Var x i) 0 c

subst :: Comp -> [(Value, Int)] -> Comp
subst c [] = c
subst c ((v, j) : as) = subst (substC c (v, j)) as