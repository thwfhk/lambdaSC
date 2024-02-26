-- # This file contains the examples of non-determinism with once.

----------------------------------------------------------------
-- ## Handlers

-- full handler for inc
DEF hInc = handler [\ x . Arr Int ((x, Int) ! mu)]
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s1 s1)
  , fwd f p k  |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

-- auxiliary function
REC concatMap = \ bs . return (
  \ f . do e <- bs == [];
           if e then return []
           else do b <- head bs;
                do bs' <- tail bs;
                do as <- f b;
                do as' <- concatMap bs' f;
                as ++ as'
  )

-- full handler for nondeterminism with once
DEF hOnce = handler [\ x . List x]
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , sc once _ p k |-> do ts <- p unit; do t <- head ts; k t
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

-- full handler for only nondeterminism
DEF hND = handler [\ x . List x]
  { return x      |-> return [x]
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

----------------------------------------------------------------
-- ## Running

-- Example in Section 2.1.5
RUN hND # (do f <- hInc # (
  op choose unit (b . if b then op inc unit (x . x+5)
                           else op inc unit (y . y+2))
); f 0)

RUN hOnce #
  sc once unit (_ . op choose unit)
               (p . do q <- op choose unit; return (p, q))


-- Interaction of inc and once:
RUN hOnce # (do f <- hInc # (
  op choose unit (b . if b then op inc unit else op inc unit)
); f 0)

RUN do f <- hInc # (hOnce # (
  op choose unit (b . if b then op inc unit else op inc unit)
)); f 0

RUN hOnce # (do f <- hInc # (
  sc once unit
    (_ . op choose unit (b . if b then op inc unit else op inc unit ))
    (x . op inc unit (y . x + y))
); f 0)