DEF hCut = handler [\ x . CutList x]
  {  return x      |->  return (opened [x])
  ,  op fail _ _   |->  return (opened [])
  ,  op choose _ k |->  do xs <- k true; do ys <- k false; append xs ys
  ,  op cut _ k    |->  do ts <- k unit; close ts
  ,  sc call _ p k |->  do ts <- p unit; do ts' <- open ts; concatMapCutList ts' k
  , fwd f p k |-> f (p, \ z . concatMapCutList z k)
  }

-- TODO: 这里有一个type inference的问题
DEF hToken = handler [\ x . Arr (List Char) ((x, List Char) ! <fail; choose; cut; call; mu>)]
  { return x      |->  return (\ s .  return (x, s))
  , op token x k |->  return (\ s .
      do b <- s == [];
         if b then op fail unit (y . absurd y)
              else do x' <- head s;
                   do xs <- tail s;
                   do b <- x == x';
                      if b then k x xs else op fail unit (y . absurd y))
  , fwd f p k |-> return (\ s . f (
      \ y . p y s ,
      \ zs . do z <- fst zs; do s' <- snd zs; k z s'
    ))
  }

REC many1 = \ p . do a <- p unit; do as <- or (many1 p) (return []); cons a as

DEF digit = \ _ . or (op token '0') (or (op token '1') (op token '2'))


-- REC exprAll = \ _ .
--   do x <- or  (do i3 <- exprAll unit; do i2 <- fst i3; do i <- snd i2;
--                do _ <- op token '+';
--                do j3 <- exprAll unit; do j2 <- fst j3; do j <- fst j2;
--                i+j)
--               (do i3 <- exprAll unit; do i2 <- fst i3; do i <- snd i2;
--                return i) ;
--   do y <- or  (do i3 <- exprAll unit; do i <- snd i3;
--                do _ <- op token '*';
--                do j3 <- exprAll unit; do j <- snd j3;
--                i*j)
--               (do i3 <- exprAll unit; do i <- snd i3;
--                return i) ;
--   do z <- or  (do ds <- many1 digit; read ds)
--               (do _ <- op token '(';
--                do i3 <- exprAll unit; do i2 <- fst i3; do i <- fst i2; 
--                do _ <- op token ')'; return i) ;
--   return ((x, y), z)


-- DEF expr = \ _ .  (do i <- term unit; do _ <- op token '+'; do j <- expr unit; i+j)
--                <> (do i <- term unit; return i)
-- DEF term = \ _ .  (do i <- factor unit; do _ <- op token '*'; do j <- factor unit; i*j)
--                <> (do i <- factor unit; return i)
-- DEF factor = \ _ .  (do ds <- many1 digit; read ds)
--                  <> (do _ <- op token '('; do i <- expr unit; do _ <- op token ')'; return i)

-- RUN hCut # (do x3 <- (do f <- hToken # exprAll unit; f "(2+5)*8");
--             do x2 <- fst x3; fst x2)

-- RUN hCut # (do x3 <- (do f <- hToken # exprAll unit; f "1"); snd x3)

-- RUN hCut # (do f <- hToken # (many1 digit); f "1")
RUN hCut # (do f <- hToken # (digit unit); f "1")
RUN do f <- hToken # (many1 digit); f "1"
RUN many1 digit

