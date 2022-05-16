DEF hInc = handler
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s s1)
  , fwd f p k  |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }


DEF hOnce = handler
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , sc once _ p k |-> do ts <- p unit; do t <- head ts; k t
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }


DEF exceptMap = \ z . return (
  \ k . case z of left e  -> return (left e)
                  right x -> k x
)
DEF hExcept = handler
  { return x       |-> return (right x)
  , op raise e k   |-> return (left e)
  , sc catch e p k |->
      do x <- p true;
      do b <- x == left e;
      if b then do y <- p false; exceptMap y  k
           else exceptMap x k
  , fwd f p k |-> f (p, \ z . exceptMap z k)
  }

DEF hState = handler
  { return x        |-> return (\ m . return (x, m))
  , op get x k      |-> return (\ m . do v <- retrieve x m; k v m)
  , op put pa k     |-> return (\ m . do m' <- update pa m; k unit m')
  , sc local xv p k |-> return (\ m . do x <- fst xv; do v <- snd xv;
                                      do um <- update xv m;
                                      do tm <- p unit um;
                                      do t <- fst tm; do m' <- snd tm;
                                      do oldv <- retrieve x m;
                                      do newm <- update (x, oldv) m';
                                      k t newm)
  , fwd f p k |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

DEF hCut = handler
  {  return x      |->  return (opened [x])
  ,  op fail _ _   |->  return (opened [])
  ,  op choose _ k |->  do xs <- k true; do ys <- k false; append xs ys
  ,  op cut _ k    |->  do ts <- k unit; close ts
  ,  sc call _ p k |->  do ts <- p unit; do ts' <- open ts; concatMapCutList ts' k
  , fwd f p k |-> f (p, \ z . concatMapCutList z k)
  }

DEF hDepth = handler
  {  return x        |->  return (\ d . return [(x, d)])
  ,  op fail _ _     |->  return (\ _ . return [])
  ,  op choose _ k   |->  return (\ d . do b <- d == 0;
                                        if b then return []
                                             else do d' <- d-1;
                                                  do xs <- k true d';
                                                  do ys <- k false d';
                                                  xs ++ ys)
  ,  sc depth d' p k |->  return (\ d . do p' <- p unit d';
                                           concatMap p' (\ vd . do v <- fst vd; k v d))
  ,  fwd f p k       |->  return (\ d . f (
      \ y . p y d ,
      \ vs . concatMap vs (\ vd . do v <- fst vd; do d <- snd vd; k v d)
     ))
  }

----------------------------------------------------------------

-- 1. cInc = op choose unit (b . if b then op inc unit else op inc unit)

RUN hOnce # (do f <- hInc # (
  op choose unit (b . if b then op inc unit else op inc unit)
); f 0)

RUN do f <- hInc # (hOnce # (
  op choose unit (b . if b then op inc unit else op inc unit)
)); f 0

----------------------------------------------------------------

-- 2. cFwd = sc once unit
--      (_ . op choose unit (b . if b then op inc unit else op inc unit))
--      (x . op inc unit (y . x + y))

RUN hOnce # (do f <- hInc # (
  sc once unit
    (_ . op choose unit (b . if b then op inc unit else op inc unit ))
    (x . op inc unit (y . x + y))
); f 0)

----------------------------------------------------------------

-- 3. cOnce = sc once unit (_ . op choose unit)
--                         (b . if b then return "heads" else return "tails")

RUN hOnce #
  sc once unit (_ . op choose unit)
               (b . if b then return "heads" else return "tails")

----------------------------------------------------------------

-- 4. cCatch = sc catch "Overflow"
--   (b . if b then do x <- op inc unit;
--                  do b <- x > 10;
--                  if b then op raise "Overflow" (y . absurd y)
--                       else return x
--        else return 10)

RUN hExcept # (do f <- hInc # (
  sc catch "Overflow"
    (b . if b then do x <- op inc unit;
                   do b <- x > 10;
                   if b then op raise "Overflow" (y . absurd y)
                        else return x
         else return 10)
); f 42)

RUN do f <- hInc # (hExcept # (
  sc catch "Overflow"
    (b . if b then do x <- op inc unit;
                   do b <- x > 10;
                   if b then op raise "Overflow" (y . absurd y)
                        else return x
         else return 10)
)); f 42

----------------------------------------------------------------

-- 5. cState = do _ <- op put (x, 10);
--             do x1 <- sc local (x, 42) (_ . op get x);
--             do x2 <- op get x;
--             return (x1, x2)


RUN do m <- newmem unit;
    do f <- hState # (
      do _ <- op put ("x", 10);
      do x1 <- sc local ("x", 42) (_ . op get "x");
      do x2 <- op get "x";
      return (x1, x2)
    );
    do x <- f m;
    fst x


----------------------------------------------------------------
-- 6. cCut

RUN hCut # (
  do b <- sc call unit (_ . 
        do y <- op choose unit;
        if y then do _ <- op cut unit; return true
             else return false );
     if b then return "heads" else return "tails"
)


----------------------------------------------------------------
-- 7. cDepth

RUN do f <- hDepth # (
    sc depth 1
      (_ . do b <- op choose unit; if b then return 1 else
            do b' <- op choose unit; if b' then return 2 else return 3)
      (x . do b <- op choose unit; if b then return x else
            do b' <- op choose unit; if b' then return 4 else
              do b'' <- op choose unit; if b'' then return 5 else return 6)
  );
  f 2


