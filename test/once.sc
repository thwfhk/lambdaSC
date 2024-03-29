-- # This file contains the examples of non-determinism with once.
-- Part of them appear in the Section 2 and 3 of the paper.

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
  , sc once _ p k |-> do ts <- p unit; do b <- ts == []; if b then return [] else do t <- head ts; k t
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

-- full handler for only nondeterminism
DEF hND = handler [\ x . List x]
  { return x      |-> return [x]
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

-- Example in Section 2.1.5
DEF cInc = \ _ .
  op choose unit (b . if b then op inc unit (x . x+5)
                           else op inc unit (y . y+2))

-- Example in Section 3.1
DEF cOnce = \ _ .
  sc once unit (_ . op choose unit)
               (p . do q <- op choose unit; return (p, q))

----------------------------------------------------------------
-- ## Running


-- ### Runnining the example in Section 2.1.5

-- first hInc then hND
RUN hND # (do f <- hInc # (cInc unit); f 0)
-- output:  [(6, 1), (3, 1)]

-- first hND then hInc
RUN do f <- hInc # (hND # (cInc unit)); f 0
-- output:  ([6, 4], 2)

-- ### Runnining the example in Section 3.1
RUN hOnce # cOnce unit
-- output:  [(true, true), (true, false)]

-- ### Running some other examples

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