DEF hND = handler [\ x : * . List x]
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

RUN hND # op choose unit (b . if b then return "heads" else return "tails")