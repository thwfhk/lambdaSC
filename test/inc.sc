-- # This file contains the examples in Section 7.

----------------------------------------------------------------
-- ## Auxiliary code

REC concatMap = \ bs . return (
  \ f . do e <- bs == [];
           if e then return []
           else do b <- head bs;
                do bs' <- tail bs;
                do as <- f b;
                do as' <- concatMap bs' f;
                as ++ as'
  )

DEF hOnce = handler [\ x . List x]
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , sc once _ p k |-> do ts <- p unit; do b <- ts == []; if b then return [] else do t <- head ts; k t
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

----------------------------------------------------------------
-- ## Implement forwarding of hInc with bind

-- We do not have the bind syntactic sugar in the implementation.
-- Instead, we directly write the desugared version here.
DEF hIncX = handler [\ x . Arr Int ((x, Int) ! mu)]
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s1 s1)
  , fwd f p k  |-> f (
      p ,
      \ x . return (\ s . do ys <- x s; do y <- fst ys; do s' <- snd ys; k y s')
    )
  }

----------------------------------------------------------------
-- ## Implement forwarding of hInc with fwd, correctly

DEF hInc = handler [\ x . Arr Int ((x, Int) ! mu)]
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s1 s1)
  , fwd f p k  |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

----------------------------------------------------------------
-- ## Running

-- run with the problematic hIncX
RUN hOnce # (do f <- hIncX # (
  sc once unit (_. op inc unit (_. op choose unit (b. return b))) (z. return z)
); f 0)
-- output:  [(true, 1), (false, 1)]

-- run with the correct hInc
RUN hOnce # (do f <- hInc # (
  sc once unit (_. op inc unit (_. op choose unit (b. return b))) (z. return z)
); f 0)
-- output:  [(true, 1)]