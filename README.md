# 𝝺sc Interpreter

This is a simple interpreter for $\lambda_{sc}$, a calculus with scoped effects & handlers.

## Getting Started

Make sure you have [stack](https://docs.haskellstack.org/en/stable/README/) installed for your device.

Build the project:
```
stack build
```

Run the interpreter using the following command:
```
stack exec lambdaSC-exe inputFileName
```

For example, `stack exec lambdaSC-exe test/once.sc` gives the following output:
```
[PARSE SUCCESS 🥳]:
  6 statements found
[TYPE INFERENCE SUCCESS 🥳]: 
  hInc : ∀a:*. ∀b:Eff. a ! <inc; b> => (Int -> (a, Int) ! b) ! b
  hOnce : ∀a:*. ∀b:Eff. a ! <fail; choose; once; b> => List a ! b
  List (Int, Int) ! a
  (List Int, Int) ! a
  List (Int, Int) ! a
  List String ! a
[EVALUATION RESULTS 🥳]:
  [(0, 1), (0, 1)]
  ([0, 1], 2)
  [(1, 2)]
  ["heads"]
```

## Files Structure

There are three main directories:

- `src` : source code of the interpreter
  - `Context.hs` : context definition and management
  - `Syntax.hs` : syntax definition and auxiliary functions
  - `Evaluation.hs` : implementation of the operational semantics
  - `TypeInference.hs` : implementation of the type inference algorithm
  - `Substitution.hs` : substitution for the type inference
  - `Lexer.hs` : lexer
  - `Parser.hs` : parser
  - `PrettyPrinter.hs` : pretty printer
- `app` : main program
  - `Main.hs` : the main program for running the interpreter
- `test` : 𝝺sc example code
  - `examples.sc` : collection of all examples in one file
  - `nd.sc` : nondeterminism
  - `once.sc` : nondeterminism with `Once` (paper Section 7.1)
  - `cut.sc` :  nondeterminism with `Cut` (paper Section 7.2)
  - `catch.sc` : exceptions (paper Section 7.3)
  - `local.sc` : local state (paper Section 7.4)
  - `depth.sc` : depth-Bounded Search (paper Section 7.5)
  - `parser.sc` : parser (paper Section 7.6)

