-- # Nondeterminism with `once` and `twice`

-- Similar to `once`, `sc twice unit (y . c1) (z . c2)` executes `c1`
-- and only keeps the first two results of it.
-- https://github.com/effekt-lang/effekt/issues/395

----------------------------------------------------------------
-- ## Handlers

-- auxiliary function
REC concatMap = \ bs . return (
  \ f . do e <- bs == [];
           if e then return []
           else do b <- head bs;
                do bs' <- tail bs;
                do as <- f b;
                do as' <- concatMap bs' f;
                as ++ as'
  )

-- handler
DEF hTwice = handler [\ x . List x]
  { return x       |-> return [x]
  , op fail _ _    |-> return []
  , op choose _ k  |-> do xs <- k true; do ys <- k false ; xs ++ ys
  , sc once _ p k  |-> do ts <- p unit; do t <- head ts; k t
  , sc twice _ p k |-> do ts <- p unit;
                       do t1 <- head ts;
                       do ts <- tail ts;
                       do t2 <- head ts;
                       do xs <- k t1;
                       do ys <- k t2;
                       xs ++ ys
  , fwd f p k |-> f (p, \ z . concatMap z k)
  }

-- `or c1 c2` is a built-in syntactic sugar for
-- `op choose unit (b . if b then c1 else c2)`

----------------------------------------------------------------
-- ## Running

RUN hTwice #
  sc twice unit (_ . or (return 1) (or (return 2) (return 3))) (z . return z)
-- output:  [1, 2]