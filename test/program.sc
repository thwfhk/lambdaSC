DEF hInc = handler [\ x : * . \ mu : Eff . Arr Int (x, Int) ! mu]
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s s1)
  , fwd f p k  |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

DEF hOnce = handler [\ x : * . \ _ : Eff . List x]
  { return x      |-> return [x]
  -- , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , sc once _ p k |-> do ts <- p unit; do t <- head ts; k t
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

DEF exceptMap = \ z . return (
  \ k . case z of left e  -> return (left e)
                  right x -> k x
)

DEF hExcept = handler [\ x : * . \ _ : Eff . Sum String x]
  { return x       |-> return (right x)
  , op raise e k   |-> return (left e)
  , sc catch e p k |->
      do x <- p true;
      do b <- x == left e;
      if b then do y <- p false; exceptMap y  k
           else exceptMap x k
  , fwd f p k |-> f (p, \ z . exceptMap z k)
  }

RUN hOnce # op choose unit (b . if b then return 1 else return 2)

RUN hOnce #
  sc once unit (_ . op choose unit)
               (b . if b then return "heads" else return "tails")

RUN hExcept #
  sc catch "SAR" (b . if b then op raise "SAR" (y . absurd y)
                      else return 10)


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

--------------------------------------------------------------

-- DEF h1st = handler 
--   { return x      |-> return x
--   , op choose _ k |-> do xs <- k true; do ys <- k false ; return xs
--   -- , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
--   , fwd f p k |-> f (p, \ z . concatMap z k)
--   }

