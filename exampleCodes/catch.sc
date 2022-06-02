DEF exceptMap = \ z . return (
  \ k . case z of left e  -> return (left e)
                  right x -> k x
)

DEF hExcept = handler [\ x : * . Sum String x]
  { return x       |-> return (right x)
  , op raise e k   |-> return (left e)
  , sc catch e p k |->
      do x <- p true;
      do b <- x == left e;
      if b then do y <- p false; exceptMap y  k
           else exceptMap x k
  , fwd f p k |-> f (p, \ z . exceptMap z k)
  }

DEF hInc = handler [\ x : * . Arr Int ((x, Int) ! mu)]
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s s1)
  , fwd f p k  |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

----------------------------------------------------------------

RUN hExcept #
  sc catch "SAR" (b . if b then op raise "SAR" (y . absurd y)
                      else return "SAR is caught!")

RUN hExcept # (do f <- hInc # (
  sc catch "Overflow"
    (b . if b then do x <- op inc unit;
                   do b <- x > 10;
                   if b then op raise "Overflow" (y . absurd y)
                        else return x
         else return 10)
); f 42)

RUN do f <- hInc # (hExcept # (
  sc catch "Overflow"
    (b . if b then do x <- op inc unit;
                   do b <- x > 10;
                   if b then op raise "Overflow" (y . absurd y)
                        else return x
         else return 10)
)); f 42