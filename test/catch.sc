DEF exceptMap = \ z . return (
  \ k . case z of left e  -> return (left e)
                  right x -> k x
)

DEF hExcept = handler [\ x . Sum String x]
  { return x       |-> return (right x)
  , op raise e k   |-> return (left e)
  , sc catch e p k |->
      do x <- p true;
      do b <- x == left e;
      if b then do y <- p false; exceptMap y  k
           else exceptMap x k
  , fwd f p k |-> f (p, \ z . exceptMap z k)
  }

DEF hInc = handler [\ x . Arr Int ((x, Int) ! mu)]
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s1 s1)
  , fwd f p k  |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

DEF incr = \ _ . 
  do x <- op inc unit;
  do b <- x > 10;
  if b then op raise "Overflow" (y . absurd y)
       else return x

DEF incr2 = \ _ .
  do _ <- incr unit; do _ <- incr unit; return unit

-- hCatch' is not well-typed, but shows the idea of modelling catch using
-- a handler
-- DEF hCatch = handler [\ x . x]
--  { return x     |-> return x
--  , op raise e k |-> return unit
--  , fwd f p k    |-> return unit
--  }
----------------------------------------------------------------

-- trivial exception and catching
RUN hExcept #
  sc catch "SAR" (b . if b then op raise "SAR" (y . absurd y)
                      else return "SAR is caught!")

-- local update semantics
RUN hExcept # (do f <- hInc # (
  sc catch "Overflow" (b . if b then incr2 unit else return unit)
); f 9)

-- global update semantics
RUN do f <- hInc # (hExcept # (
  sc catch "Overflow" (b . if b then incr2 unit else return unit)
)); f 9

-- global update semantics via scoped-effects-as-handlers
-- RUN do f <- hInc # (hCatch # incr2 unit); f 9