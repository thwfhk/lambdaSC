DEF hState = handler [\ x . Arr (Mem String Int) ((x, Mem String Int) ! mu)]
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

----------------------------------------------------------------

RUN do m <- newmem unit;
    do f <- hState # (
      do _ <- op put ("x", 10);
      do x1 <- sc local ("x", 42) (_ . op get "x");
      do x2 <- op get "x";
      return (x1, x2)
    );
    do x <- f m;
    fst x
