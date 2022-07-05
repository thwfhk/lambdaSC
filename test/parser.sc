DEF hCut = handler [\ x . CutList x]
  {  return x      |->  return (opened [x])
  ,  op fail _ _   |->  return (opened [])
  ,  op choose _ k |->  do xs <- k true; do ys <- k false; append xs ys
  ,  op cut _ k    |->  do ts <- k unit; close ts
  ,  sc call _ p k |->  do ts <- p unit; do ts' <- open ts; concatMapCutList ts' k
  ,  fwd f p k |-> f (p, \ z . concatMapCutList z k)
  }

-- TODO: 这里有一个type inference的问题
DEF hToken = handler [\ x . Arr (List Char) ((x, List Char) ! <fail | mu>)]
  { return x     |->  return (\ s .  return (x, s))
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

DEF digit = \ _ .
  or (op token '0') (
  or (op token '1') (
  or (op token '2') (
  or (op token '3') (
  or (op token '4') (
  or (op token '5') (
  or (op token '6') (
  or (op token '7') (
  or (op token '8') (op token '9')
    ))))))))

-- Because the interpreter does not support mutual recursion, we define
-- expr, term, and factor together.
REC exprAll = \ index .
  do b <- index == 1; if b then
          or  (do i <- exprAll 2; do _ <- op token '+'; do j <- exprAll 1; i+j)
              (exprAll 2)
     else do b <- index == 2; if b then
          or  (do i <- exprAll 3; do _ <- op token '*'; do j <- exprAll 2; i*j)
              (exprAll 3)
     else or  (do ds <- many1 digit; read ds)
              (do _ <- op token '('; do i <- exprAll 1; do _ <- op token ')'; return i)

-- The improved version of expr using the cut operation.
REC exprAll' = \ index .
  do b <- index == 1; if b then
          do i <- exprAll' 2;
             sc call unit (_ . or (do _ <- op token '+'; do _ <- op cut unit; do j <- exprAll' 1; i+j)
                                  (return i))
     else do b <- index == 2; if b then
          or  (do i <- exprAll' 3; do _ <- op token '*'; do j <- exprAll' 2; i*j)
              (exprAll' 3)
     else or  (do ds <- many1 digit; read ds)
              (do _ <- op token '('; do i <- exprAll' 1; do _ <- op token ')'; return i)


RUN hCut # (do f <- hToken # exprAll 1; f "(2+5)*8")

RUN hCut # (do f <- hToken # exprAll' 1; f "(2+5)*8")