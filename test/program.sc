DEF h = handler {
  return x |-> return [x],
  op choose x k |-> do xs <- k true; do ys <- k false ; return (xs, ys),
  fwd f p k |-> return unit
  }

RUN h # (op choose unit (b . if b then return "heads" else return "tails"))