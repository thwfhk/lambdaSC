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

----------------------------------------------------------------

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

RUN hOnce #
  sc once unit (_ . op choose unit)
               (b . if b then return "heads" else return "tails")
