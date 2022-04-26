DEF hInc = handler
  { return x |-> return (\ s . return (x, s))
  , op inc x k |-> return (\ s . do k' <- k s; do s1 <- (s + 1); k' s1)
  , fwd f p k |-> return (\ s . f (
      \ y . do p' <- p y; p' s ,
      \ zs . do z <- fst zs; do s' <- snd zs; do k' <- k z; k' s'
    ))
  }


DEF hOnce = handler
  { return x |-> return [x]
  , op fail x k |-> return []
  , op choose x k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , sc once x p k |-> do ts <- p unit; do t <- head ts; k t
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }


DEF exceptMap = \ z . return (
  \ k . case z of left e -> return (left e)
                  right x -> k x
)
DEF hExcept = handler
  { return x |-> return (right x)
  , op raise e k |-> return (left e)
  , sc catch e p k |->
      do x <- p true;
      do b <- x == left e;
      if b then do y <- p false; do f <- exceptMap y; f k
           else do f <- exceptMap x; f k
  , fwd f p k |-> f (p, \ z . do f <- exceptMap z; f k)
  }

DEF hState = handler
  { return x |-> return (\ m . return (x, m))
  , op get x k |-> return (\ m . do v <- retrieve x m;
                                 do k' <- k v; k' m)
  , op put pa k |-> return (\ m . do k' <- k unit;
                                  do m' <- update pa m; k' m')
  , sc local xv p k |-> return (\ m . do x <- fst xv; do v <- snd xv;
                                      do um <- update xv m;
                                      do p' <- p unit;
                                      do tm <- p' um;
                                      do t <- fst tm; do m' <- snd tm;
                                      do k' <- k t;
                                      do oldv <- retrieve x m;
                                      do newm <- update (x, oldv) m';
                                      k' newm)
  , fwd f p k |-> return (\ s . f (
      \ y . do p' <- p y; p' s ,
      \ zs . do z <- fst zs; do s' <- snd zs; do k' <- k z; k' s'
    ))
  }

----------------------------------------------------------------

-- 1. cInc = op choose unit (b . if b
--                               then op inc unit (t.return t)
--                               else op inc unit (t.return t))

RUN hOnce # (do f <- hInc # (
  op choose unit (b . if b then op inc unit (t.return t) else op inc unit (t.return t))
); f 0)

RUN do f <- hInc # (hOnce # (
  op choose unit (b . if b then op inc unit (t.return t) else op inc unit (t.return t))
)); f 0

----------------------------------------------------------------

-- 2. cFwd = sc once unit
--      (_ . op choose unit (b . if b
--                                  then op inc unit (y.return y)
--                                  else op inc unit (y.return y)))
--      (x . op inc unit (y . do z <- x + y; return z))

RUN hOnce # (do f <- hInc # (
  sc once unit
    (_ . op choose unit (b . if b
                             then op inc unit (y.return y)
                             else op inc unit (y.return y)))
    (x . op inc unit (y . do z <- x + y; return z))
); f 0)

----------------------------------------------------------------

-- 3. cOnce = sc once unit (_ . op choose unit (y . return y))
--                         (b . if b then return "heads" else return "tails")

RUN hOnce #
  sc once unit (_ . op choose unit (y . return y))
               (b . if b then return "heads" else return "tails")

----------------------------------------------------------------

-- 4. cCatch = sc catch "Overflow"
--   (b . if b then do x <- op inc unit (y.return y)
--                  do b <- x > 10;
--                  if b then op raise "Overflow" (y . absurd y)
--                       else return x
--        else return 10)

RUN hExcept # (do f <- hInc # (
  sc catch "Overflow"
    (b . if b then do x <- op inc unit (y.return y);
                   do b <- x > 10;
                   if b then op raise "Overflow" (y . absurd y)
                        else return x
         else return 10)
    (z . return z)
); f 42)

RUN do f <- hInc # (hExcept # (
  sc catch "Overflow"
    (b . if b then do x <- op inc unit (y.return y);
                   do b <- x > 10;
                   if b then op raise "Overflow" (y . absurd y)
                        else return x
         else return 10)
    (z . return z)
)); f 42

----------------------------------------------------------------

-- 5. cState = do _ <- op put (x, 10) (y.return y);
--             do x1 <- sc local (x, 42) (_ . op get x (y.return y));
--             do x2 <- op get x (y.return y);
--             return (x1, x2)


RUN do m <- newmem unit;
    do f <- hState # (
      do _ <- op put ("x", 10) (y.return y);
      do x1 <- sc local ("x", 42) (_ . op get "x" (y.return y)) (z.return z);
      do x2 <- op get "x" (y.return y);
      return (x1, x2)
    );
    do x <- f m;
    fst x