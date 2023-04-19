DEF hCut = handler [\ x . CutList x]
  {  return x      |->  return (opened [x])
  ,  op fail _ _   |->  return (opened [])
  ,  op choose _ k |->  do xs <- k true; do ys <- k false; appendCutList xs ys
  ,  op cut _ k    |->  do ts <- k unit; close ts
  ,  sc call _ p k |->  do ts <- p unit; do ts' <- open ts; concatMapCutList ts' k
  ,  fwd f p k |-> f (p, \ z . concatMapCutList z k)
  }

----------------------------------------------------------------

RUN hCut # (
  do b <- sc call unit (_ . 
        do y <- op choose unit;
        if y then do _ <- op cut unit; return true
             else return false );
     if b then return "heads" else return "tails"
)
