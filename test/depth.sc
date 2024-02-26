-- # This file contains the examples in Section 9.4.

REC concatMap = \ bs . return (
  \ f . do e <- bs == [];
           if e then return []
           else do b <- head bs;
                do bs' <- tail bs;
                do as <- f b;
                do as' <- concatMap bs' f;
                as ++ as'
  )

-- handler for non-determinism with depth
DEF hDepth = handler [\ x . Arr Int (List (x, Int) ! mu)]
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

-- alternative implementation of a handler for non-determinism with depth
DEF hDepth2 = handler [\ x . Arr Int (List (x, Int) ! mu)]
  {  return x        |->  return (\ d . return [(x, d)])
  ,  op fail _ _     |->  return (\ _ . return [])
  ,  op choose _ k   |->  return (\ d . do b <- d == 0;
                                        if b then return []
                                        else do d' <- d-1;
                                             do xs <- k true d';
                                             do ys <- k false d';
                                             xs ++ ys)
  ,  sc depth d' p k |->  return (\ d . do p' <- p unit d';
                                        concatMap p' (\ vd . do v <- fst vd;
                                                             do dm <- d-d';
                                                             k v dm))
  -- This implementation of the depth clause consumes the global depth d
  -- when doing the local search with depth bound d'. Thus, we use d-d' as
  -- the depth bound for the continuation.
  ,  fwd f p k       |->  return (\ d . f (
      \ y . p y d ,
      \ vs . concatMap vs (\ vd . do v <- fst vd; do d <- snd vd; k v d)
     ))
  }

----------------------------------------------------------------
-- ## Running

DEF cDepth = \_ .
    sc depth 1
      (_ . do b <- op choose unit; if b then return 1 else
            do b' <- op choose unit; if b' then return 2 else return 3)
      (x . do b <- op choose unit; if b then return x else
            do b' <- op choose unit; if b' then return 4 else
              do b'' <- op choose unit; if b'' then return 5 else return 6)

-- run the first implementation hDepth
RUN do f <- hDepth # (cDepth unit); f 2
-- output:  [(1, 1), (4, 0)]

-- run the second implementation hDepth2
RUN do f <- hDepth2 # (cDepth unit); f 2
-- output: [(1, 0)]
