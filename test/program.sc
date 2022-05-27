DEF h1st = handler
  { return x      |-> return x
  , op choose _ k |-> do xs <- k true; do ys <- k false ; return xs
  -- , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }


-- DEF f = \ x . op choose unit (b . fst x)

RUN h1st # op choose unit (b . return 1)