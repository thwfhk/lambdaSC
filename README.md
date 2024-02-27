# 𝝺sc Interpreter

This is a simple interpreter for $\lambda_{sc}$, a calculus for scoped effects & handlers.

The interpreter supports parsing, type inference, evaluation, and printing.

## Getting Started

Make sure you have [stack](https://docs.haskellstack.org/en/stable/README/) installed.

Build the interpreter:

```
stack build
```

Run the interpreter with a given file using the following command:

```
stack exec lambdaSC-exe inputFileName
```

For example, running `stack exec lambdaSC-exe test/intro.sc` gives the following output:

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
- `test` : 𝝺sc examples
  - `intro.sc` : an introduction file to the syntax (the syntax supported by the interpreter is slightly different from the paper)
  - `once.sc` : nondeterminism with `once` (paper Section 2 and 3)
  - `inc.sc` : forwarding for the handler of `inc` (paper Section 7)
  - `exceptions.sc` : exceptions (paper Section 9.1)
  - `localread.sc` : reader with local (paper Section 9.2)
  - `cut.sc` :  nondeterminism with `cut` (paper Section 9.3)
  - `depth.sc` : depth-Bounded Search (paper Section 9.4)
  - `parser.sc` : parser (paper Section 9.5)
  - `localstate.sc` : local state

## Evaluating the Artifact

We propose to evaluate the artifact by running `stack exec lambdaSC-exe inputFileName` and replacing `inputFileName` with each file name in the `test` directory. This will show the results of all non-trivial examples appearing in the paper.

The correspondence between examples in the paper and test files is shown as follows:

- `test/once.sc` contains some examples in Section 2 and 3 that use non-determinism and `once`.
- `test/inc.sc` contains the examples in Section 7 including both the problematic and correct implementations of forwarding for the handler of `inc`
- `test/exceptions.sc` contains the examples in Section 9.1 including catch as a handler and catch as a scoped effect
- `test/localread.sc` contains the examples in Section 9.2 including local as a handler and local as a scoped effect
- `test/cut.sc` contains the examples in Section 9.3
- `test/depth.sc` contains the examples in Section 9.4
- `test/parser.sc` contains the examples in Section 9.5