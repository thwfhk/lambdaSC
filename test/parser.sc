RUN letrec f = \ x . do b <- x == 0; 
                        if b then return 100
                        else f 0
    in f 1


-- DEF hToken = handler
--   { return x      |->  return (\ s .  return (x, s))
--   , op symbol x k |->  return (\ s .
--       do b <- s == [];
--          if b then op fail unit (y . absurd y)
--               else do x' <- head s;
--                    do xs <- tail s;
--                    do b <- x == x';
--                       if b then k x xs else op fail unit (y . absurd y))
--   , fwd f p k |-> return (\ s . f (
--       \ y . p y s ,
--       \ zs . do z <- fst zs; do s' <- snd zs; k z s'
--     ))
--   }
  
-- TODO: Recursion needed !
-- DEF digit = \ _ .  op token '0' 
-- 
-- DEF expr = \ _ .  (do i <- term unit; do _ <- op token '+'; do j <- expr unit; i+j)
--                <> (do i <- term unit; return i)
-- 
-- DEF term = \ _ .  (do i <- factor unit; do _ <- op token '*'; do j <- factor unit; i*j)
--                <> (do i <- factor unit; return i)
-- 
-- DEF factor = \ _ .  (do ds <- many1 digit; read ds)
--                  <> (do _ <- op token '('; do i <- expr unit; do _ <- op token ')'; return i)