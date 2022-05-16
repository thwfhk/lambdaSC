DEF hDepth = handler
  {  return x        |->  return (\ d . return [(x, d)])
  ,  op fail _ _     |->  return (\ _ . return [])
  ,  op choose _ k   |->  return (\ d . do b <- d == 0;
                                        if b then return []
                                             else do d' <- d-1;
                                                  do xs <- k true d';
                                                  do ys <- k false d';
                                                  xs ++ ys)
  ,  sc depth d' p k |->  return (\ d . do p' <- p unit d';
                                           concatMap p' (\ vd . do v <- fst vd; k v d))
  ,  fwd f p k       |->  return (\ d . f (
      \ y . p y d ,
      \ vs . concatMap vs (\ vd . do v <- fst vd; do d <- snd vd; k v d)
     ))
  }

----------------------------------------------------------------

RUN do f <- hDepth # (
    sc depth 1
      (_ . do b <- op choose unit; if b then return 1 else
            do b' <- op choose unit; if b' then return 2 else return 3)
      (x . do b <- op choose unit; if b then return x else
            do b' <- op choose unit; if b' then return 4 else
              do b'' <- op choose unit; if b'' then return 5 else return 6)
  );
  f 2
