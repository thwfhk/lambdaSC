module CodeString where

nd = "\
  \DEF hND = handler \n\
  \  { return x      |-> return [x] \n\
  \  , op fail _ _   |-> return [] \n\
  \  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys \n\
  \  , fwd f p k |-> f (p, \\ z . concatMap z k) \n\
  \  } \n\
  \ \n\
  \RUN hND # op choose unit (b . if b then return \"heads\" else return \"tails\") \n\
  \"

local = "\
  \DEF hState = handler \n\
  \  { return x        |-> return (\\ m . return (x, m)) \n\
  \  , op get x k      |-> return (\\ m . do v <- retrieve x m; k v m) \n\
  \  , op put pa k     |-> return (\\ m . do m' <- update pa m; k unit m') \n\
  \  , sc local xv p k |-> return (\\ m . do x <- fst xv; do v <- snd xv; \n\
  \                                      do um <- update xv m; \n\
  \                                      do tm <- p unit um; \n\
  \                                      do t <- fst tm; do m' <- snd tm; \n\
  \                                      do oldv <- retrieve x m; \n\
  \                                      do newm <- update (x, oldv) m'; \n\
  \                                      k t newm) \n\
  \  , fwd f p k |-> return (\\ s . f ( \n\
  \      \\ y . p y s , \n\
  \      \\ zs . do z <- fst zs; do s' <- snd zs; k z s' \n\
  \    )) \n\
  \  } \n\
  \ \n\
  \---------------------------------------------------------------- \n\
  \ \n\
  \RUN do m <- newmem unit; \n\
  \    do f <- hState # ( \n\
  \      do _ <- op put (\"x\", 10); \n\
  \      do x1 <- sc local (\"x\", 42) (_ . op get \"x\"); \n\
  \      do x2 <- op get \"x\"; \n\
  \      return (x1, x2) \n\
  \    ); \n\
  \    do x <- f m; \n\
  \    fst x \n\
  \ \n\
  \"

cut = "\
  \DEF hCut = handler \n\
  \  {  return x      |->  return (opened [x]) \n\
  \  ,  op fail _ _   |->  return (opened []) \n\
  \  ,  op choose _ k |->  do xs <- k true; do ys <- k false; append xs ys \n\
  \  ,  op cut _ k    |->  do ts <- k unit; close ts \n\
  \  ,  sc call _ p k |->  do ts <- p unit; do ts' <- open ts; concatMapCutList ts' k \n\
  \  , fwd f p k |-> f (p, \\ z . concatMapCutList z k) \n\
  \  } \n\
  \ \n\
  \---------------------------------------------------------------- \n\
  \ \n\
  \RUN hCut # ( \n\
  \  do b <- sc call unit (_ .  \n\
  \        do y <- op choose unit; \n\
  \        if y then do _ <- op cut unit; return true \n\
  \             else return false ); \n\
  \     if b then return \"heads\" else return \"tails\" \n\
  \) \n\
  \ \n\
  \"

once = "\
  \DEF hInc = handler \n\
  \  { return x   |-> return (\\ s . return (x, s)) \n\
  \  , op inc _ k |-> return (\\ s . do s1 <- (s + 1); k s s1) \n\
  \  , fwd f p k  |-> return (\\ s . f ( \n\
  \      \\ y . p y s , \n\
  \      \\ zs . do z <- fst zs; do s' <- snd zs; k z s' \n\
  \    )) \n\
  \  } \n\
  \ \n\
  \DEF hOnce = handler \n\
  \  { return x      |-> return [x] \n\
  \  , op fail _ _   |-> return [] \n\
  \  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys \n\
  \  , sc once _ p k |-> do ts <- p unit; do t <- head ts; k t \n\
  \  , fwd f p k |-> f (p, \\ z . concatMap z k) \n\
  \  } \n\
  \ \n\
  \---------------------------------------------------------------- \n\
  \ \n\
  \RUN hOnce # (do f <- hInc # ( \n\
  \  op choose unit (b . if b then op inc unit else op inc unit) \n\
  \); f 0) \n\
  \ \n\
  \RUN do f <- hInc # (hOnce # ( \n\
  \  op choose unit (b . if b then op inc unit else op inc unit) \n\
  \)); f 0 \n\
  \ \n\
  \RUN hOnce # (do f <- hInc # ( \n\
  \  sc once unit \n\
  \    (_ . op choose unit (b . if b then op inc unit else op inc unit )) \n\
  \    (x . op inc unit (y . x + y)) \n\
  \); f 0) \n\
  \ \n\
  \RUN hOnce # \n\
  \  sc once unit (_ . op choose unit) \n\
  \               (b . if b then return \"heads\" else return \"tails\") \n\
  \ \n\
  \"

depth = "\
  \DEF hDepth = handler \n\
  \  {  return x        |->  return (\\ d . return [(x, d)]) \n\
  \  ,  op fail _ _     |->  return (\\ _ . return []) \n\
  \  ,  op choose _ k   |->  return (\\ d . do b <- d == 0; \n\
  \                                        if b then return [] \n\
  \                                             else do d' <- d-1; \n\
  \                                                  do xs <- k true d'; \n\
  \                                                  do ys <- k false d'; \n\
  \                                                  xs ++ ys) \n\
  \  ,  sc depth d' p k |->  return (\\ d . do p' <- p unit d'; \n\
  \                                           concatMap p' (\\ vd . do v <- fst vd; k v d)) \n\
  \  ,  fwd f p k       |->  return (\\ d . f ( \n\
  \      \\ y . p y d , \n\
  \      \\ vs . concatMap vs (\\ vd . do v <- fst vd; do d <- snd vd; k v d) \n\
  \     )) \n\
  \  } \n\
  \ \n\
  \---------------------------------------------------------------- \n\
  \ \n\
  \RUN do f <- hDepth # ( \n\
  \    sc depth 1 \n\
  \      (_ . do b <- op choose unit; if b then return 1 else \n\
  \            do b' <- op choose unit; if b' then return 2 else return 3) \n\
  \      (x . do b <- op choose unit; if b then return x else \n\
  \            do b' <- op choose unit; if b' then return 4 else \n\
  \              do b'' <- op choose unit; if b'' then return 5 else return 6) \n\
  \  ); \n\
  \  f 2 \n\
  \ \n\
  \"

catch = "\
  \DEF exceptMap = \\ z . return ( \n\
  \  \\ k . case z of left e  -> return (left e) \n\
  \                  right x -> k x \n\
  \) \n\
  \ \n\
  \DEF hExcept = handler \n\
  \  { return x       |-> return (right x) \n\
  \  , op raise e k   |-> return (left e) \n\
  \  , sc catch e p k |-> \n\
  \      do x <- p true; \n\
  \      do b <- x == left e; \n\
  \      if b then do y <- p false; exceptMap y  k \n\
  \           else exceptMap x k \n\
  \  , fwd f p k |-> f (p, \\ z . exceptMap z k) \n\
  \  } \n\
  \ \n\
  \DEF hInc = handler \n\
  \  { return x   |-> return (\\ s . return (x, s)) \n\
  \  , op inc _ k |-> return (\\ s . do s1 <- (s + 1); k s s1) \n\
  \  , fwd f p k  |-> return (\\ s . f ( \n\
  \      \\ y . p y s , \n\
  \      \\ zs . do z <- fst zs; do s' <- snd zs; k z s' \n\
  \    )) \n\
  \  } \n\
  \ \n\
  \---------------------------------------------------------------- \n\
  \ \n\
  \RUN hExcept # (do f <- hInc # ( \n\
  \  sc catch \"Overflow\" \n\
  \    (b . if b then do x <- op inc unit; \n\
  \                   do b <- x > 10; \n\
  \                   if b then op raise \"Overflow\" (y . absurd y) \n\
  \                        else return x \n\
  \         else return 10) \n\
  \); f 42) \n\
  \ \n\
  \RUN do f <- hInc # (hExcept # ( \n\
  \  sc catch \"Overflow\" \n\
  \    (b . if b then do x <- op inc unit; \n\
  \                   do b <- x > 10; \n\
  \                   if b then op raise \"Overflow\" (y . absurd y) \n\
  \                        else return x \n\
  \         else return 10) \n\
  \)); f 42 \n\
  \"

