-- define a handler for non-determinism using the keyword DEF
-- write the type annotation of handlers in the brackets

REC concatMap = \ bs . return (
  \ f . do e <- bs == [];
           if e then return []
           else do b <- head bs;
                do bs' <- tail bs;
                do as <- f b;
                do as' <- concatMap bs' f;
                as ++ as'
  )
DEF hND = handler [\ x . List x]
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , fwd f p k     |-> f (p, \ z . concatMap z k)
  }


-- apply the handler to a computation using the keyword RUN

RUN hND # op choose unit (b . if b then return "heads" else return "tails")


-- or directly write the definition of the handler in the computation
-- instead of defining first

RUN handler [\ x . List x]
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , fwd f p k |-> f (p, \ z . concatMap z k)
  } # op choose unit (b . if b then return "heads" else return "tails")
