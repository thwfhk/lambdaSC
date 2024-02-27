-- Define non-recursive functions using the keyword DEF
DEF f = \ x . x + 1

-- Define recursive functions using the keyword REC
REC g = \ x . do b <- x == 0;
                 if b then return 0
                 else do x' <- x - 1;
                      do s <- g x';
                      x + s

-- For example, we can define `concatMap` as follows
REC concatMap = \ bs . return (
  \ f . do e <- bs == [];
           if e then return []
           else do b <- head bs;
                do bs' <- tail bs;
                do as <- f b;
                do as' <- concatMap bs' f;
                as ++ as'
  )

-- The handler `hND` for non-determinism
-- The carrier of the handler is annotated in brackets
DEF hND = handler [\ x . List x]
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , fwd f p k     |-> f (p, \ z . concatMap z k)
  }

-- The type inference gives the following type to `hND`:
--   hND : ∀a:*. ∀b:Eff. a ! <fail; choose | b> => List a ! b
-- Different from the paper, we add kinds to explicitly distinguish between type
-- variables, and we use `|` to seperate the row type variable from other labels.
----------------------------------------------------------------

-- Run a computation using the keyword RUN
-- Note that all RUN statements must appear after all DEF and REC statements
RUN g 5

-- Apply the handler `hND` to a non-deterministic computation using #
RUN hND # op choose unit (b . if b then return "heads" else return "tails")

-- You can also directly write the definition of the handler instead of defining it first
RUN handler [\ x . List x]
  { return x      |-> return [x]
  , op fail _ _   |-> return []
  , op choose _ k |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , fwd f p k |-> f (p, \ z . concatMap z k)
  } # op choose unit (b . if b then return "heads" else return "tails")
