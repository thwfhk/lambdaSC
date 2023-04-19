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
  7 statements found
[TYPE INFERENCE SUCCESS 🥳]: 
  f : ∀a:Eff. Int -> Int ! a
  g : ∀a:Eff. Int -> Int ! a
  concatMap : ∀a:*. ∀b:*. ∀c:Eff. List a -> ((a -> List b ! c) -> List b ! c) ! c
  hND : ∀a:*. ∀b:Eff. a ! <fail; choose | b> => List a ! b
  Int ! a
  List List Char ! a
  List List Char ! a
[EVALUATION RESULTS 🥳]:
 15
 ["heads", "tails"]
 ["heads", "tails"]
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
  - `once.sc` : nondeterminism with `Once` (paper Section 3 and 5)
  - `catch.sc` : exceptions (paper Section 7.1)
  - `localread.sc` : reader with local (paper Section 7.2)
  - `cut.sc` :  nondeterminism with `Cut` (paper Section 7.3)
  - `depth.sc` : depth-Bounded Search (paper Section 7.4)
  - `parser.sc` : parser (paper Section 7.5)
  - `local.sc` : local state (bonus)

## Evaluating the Artifact

We propose to evaluate the artifact by running `stack exec
lambdaSC-exe inputFileName` and replacing `inputFileName` with each
file name in the `test` directory. This will show the results of all
the examples relevant to scoped effects appearing in the paper.