DEF hInc = handler [\ x : * . Arr Int ((x, Int) ! mu)]
  { return x   |-> return (\ s . return (x, s))
  , op inc _ k |-> return (\ s . do s1 <- (s + 1); k s s1)
  , fwd f p k  |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

DEF hOnce = handler [\ x : * . List x]
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , sc once _ p k |-> do ts <- p unit; do t <- head ts; k t
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }


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

DEF hCut = handler [\ x : * . CutList x]
  {  return x      |->  return (opened [x])
  ,  op fail _ _   |->  return (opened [])
  ,  op choose _ k |->  do xs <- k true; do ys <- k false; append xs ys
  ,  op cut _ k    |->  do ts <- k unit; close ts
  ,  sc call _ p k |->  do ts <- p unit; do ts' <- open ts; concatMapCutList ts' k
  , fwd f p k |-> f (p, \ z . concatMapCutList z k)
  }

----------------------------------------------------------------

-- 3. cOnce = sc once unit (_ . op choose unit)
--                         (b . if b then return "heads" else return "tails")

RUN hOnce #
  sc once unit (_ . op choose unit)
               (b . if b then return "heads" else return "tails")

----------------------------------------------------------------

-- 4. cCatch = sc catch "Overflow"
--   (b . if b then do x <- op inc unit;
--                  do b <- x > 10;
--                  if b then op raise "Overflow" (y . absurd y)
--                       else return x
--        else return 10)

RUN hExcept #
  sc catch "SAR" (b . if b then op raise "SAR" (y . absurd y)
                      else return "SAR is caught!")

----------------------------------------------------------------
-- 6. cCut

RUN hCut # (
  do b <- sc call unit (_ . 
        do y <- op choose unit;
        if y then do _ <- op cut unit; return true
             else return false );
     if b then return "heads" else return "tails"
)
