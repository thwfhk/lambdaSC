# 𝝺sc Interpreter

This is a simple interpreter for $\lambda_{sc}$, a calculus for scoped effects & handlers.

The interpreter supports parsing, type inference, and evaluation.

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
  8 statements found
[TYPE INFERENCE SUCCESS 🥳]: 
  hInc : ∀a:*. ∀b:Eff. a ! <inc | b> => (Int -> (a, Int) ! b) ! b
  concatMap : ∀a:*. ∀b:*. ∀c:Eff. List a -> ((a -> List b ! c) -> List b ! c) ! c
  hOnce : ∀a:*. ∀b:Eff. a ! <fail; choose; once | b> => List a ! b
  (Int, Int) ! a
  List (Int, Int) ! a
  (List Int, Int) ! a
  List (Int, Int) ! a
  List List Char ! a
[EVALUATION RESULTS 🥳]:
 (0, 1)
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
- `test` : 𝝺sc example codes
  - `intro.sc` : an introduction file to the syntax (the syntax supported by the interpreter is slightly different from the paper)
  - `once.sc` : nondeterminism with `Once` (paper Section 7.1)
  - `cut.sc` :  nondeterminism with `Cut` (paper Section 7.2)
  - `catch.sc` : exceptions (paper Section 7.3)
  - `local.sc` : local state (paper Section 7.4)
  - `depth.sc` : depth-Bounded Search (paper Section 7.5)
  - `parser.sc` : parser (paper Section 7.6)
  - `examples.sc` : collection of all examples in one file

## Evaluating the Artifact

We propose to evaluate the artifact by running `stack exec lambdaSC-exe inputFileName` and replacing `inputFileName` with each file name in the `test` directory.
This will show the results of all the examples appearing in the paper.