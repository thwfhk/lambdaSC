-- # This file contains the examples in Section 9.2.

----------------------------------------------------------------
-- ## Local as a handler

DEF hFoo = handler [\ x . x]
  { return x    |-> return x
  , op foo _ k  |-> op ask unit (y . k y)
  , fwd f p k   |-> f (p, k)
  }

DEF hReadX = handler [\ x . Arr Int (x ! mu)]
  { return x        |-> return (\ s . return x)
  , op ask _ k      |-> return (\ s . k s s)
  , fwd _ _ _       |-> undefined unit          -- never used
  }

DEF cLocalX = \ _ .
  do x <- op ask unit;
  do y <- op foo unit;
  handler [\ x . x] {
      return x   |-> return x
    , op ask _ k |-> do x <- op ask unit; do x2 <- (2*x); k x2
    , fwd _ _ _  |-> undefined unit             -- never used
  } # (
    do z <- op ask unit;
    do u <- op foo unit;
    return (x, (y, (z, u)))
  )


----------------------------------------------------------------
-- ## Local as a scoped effect

-- handler for ask and lread (called local in the paper)
DEF hRead = handler [\ x . Arr Int (x ! mu)]
  { return x        |-> return (\ s . return x)
  , op ask _ k      |-> return (\ s . k s s)
  , sc lread f p k  |-> return (\ s . do fs <- f s;
                                      do x <- p unit fs;
                                      k x s)
  , fwd f p k       |-> return (\ s . f (
      \ y . p y s ,
      \ z . k z s
    ))
  }

DEF cLocal = \ _ .
  do x <- op ask unit;
  do y <- op foo unit;
  sc lread (\ x . 2 * x)
    (_.
      do z <- op ask unit;
      do u <- op foo unit;
      return (x, (y, (z, u)))
    ) (t . return t)

----------------------------------------------------------------
-- ## Running

-- running with catch as a handler
RUN do c <- hReadX # (hFoo # (cLocalX unit)); c 1
-- output:  (1, (1, (2, 1)))

-- running with catch as a scoped operation
RUN do c <- hRead # (hFoo # (cLocal unit)); c 1
-- output:  (1, (1, (2, 2)))