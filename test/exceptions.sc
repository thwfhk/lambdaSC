-- # This file contains the examples in Section 9.1.

----------------------------------------------------------------
-- ## Catch as a handler

DEF hExceptX = handler [\ x . Sum String x]
  { return x       |-> return (right x)
  , op raise e k   |-> return (left e)
  , fwd _ _ _      |-> undefined unit -- never used
  }

DEF incr = \ _ .
  do x <- op inc unit;
  do b <- x > 10;
  if b then op raise "Overflow" (y . absurd y)
       else return x

DEF cCatchX = \ _ .
  do _ <- incr unit;
  handler [\ x . x] {
      return x     |-> return x
    , op raise e k |-> anytype (return "fail") -- hack with anytype because lambda_sc
                                               -- only allows polymorphic handlers
    , fwd _ _ _    |-> undefined unit          -- never used
  } # (do _ <- incr unit; do _ <- incr unit; return "success")

----------------------------------------------------------------
-- ## Catch as a scoped operation

-- auxiliary function
DEF exceptMap = \ z . return (
  \ k . case z of left e  -> return (left e)
                  right x -> k x
)

-- handler for raise and catch
DEF hExcept = handler [\ x . Sum String x]
  { return x       |-> return (right x)
  , op raise e k   |-> return (left e)
  , sc catch e p k |->
      do x <- p true;
      do b <- x == left e;
      if b then do y <- p false; exceptMap y  k
           else exceptMap x k
  , fwd f p k      |-> f (p, \ z . exceptMap z k)
  }

-- handler for inc
DEF hInc = handler [\ x . Arr Int ((x, Int) ! mu)]
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s1 s1)
  , fwd f p k  |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

DEF cCatch = \ _ .
  do _ <- incr unit;
  sc catch "Overflow" (b . if b then do _ <- incr unit; do _ <- incr unit; return "success"
                           else return "fail")

----------------------------------------------------------------
-- ## Test the evaluation results

-- ### Running with catch as a handler

-- global update semantics
RUN do f <- hInc # (hExceptX # cCatchX   unit); f 8

-- expect local update semantics but get global update semantics
RUN hExceptX # (do f <- hInc # cCatchX unit; f 8)

-- ### Running with catch as a scoped operation

-- global update semantics
RUN do f <- hInc # (hExcept # cCatch unit); f 8

-- local update semantics
RUN hExcept # (do f <- hInc # cCatch unit; f 8)