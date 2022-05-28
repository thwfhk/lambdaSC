DEF hOnce = handler [\ x . List x]
  { return x      |-> return [x]
  -- , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , sc once _ p k |-> do ts <- p unit; do t <- head ts; k t
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

RUN hOnce # op choose unit (b . if b then return 1 else return 2)

RUN hOnce #
  sc once unit (_ . op choose unit)
               (b . if b then return "heads" else return "tails")

--------------------------------------------------------------

-- DEF h1st = handler 
--   { return x      |-> return x
--   , op choose _ k |-> do xs <- k true; do ys <- k false ; return xs
--   -- , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
--   , fwd f p k |-> f (p, \ z . concatMap z k)
--   }

