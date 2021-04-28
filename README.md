# Tutorial on implementing Hoare logic for imperative programs in Haskell

This is the source code repository for my paper `Tutorial on implementing Hoare logic for imperative programs in Haskell`. In it you will find:

- `Common.hs`, `PrettyPrinter.hs` - Various utility functions
- `Gentzen.hs` - Implementation of Propositional calculus
- `TNT.hs` - Implementation of Typographical Number Theory
- `Hoare.hs` - Implementation of Hoare logic (on top of Propositional calculus + Number theory)
- `Imp.hs` - Implementation of a simple imperative programming language (the commands correspond to the rules of Hoare logic)

## Prerequisites

Make sure you have the [Haskell Tool Stack](https://haskellstack.org/) installed.

## Running the examples

Check the files in the `examples` folder - each implementation of the system has a corresponding example file.

For instance, to run the proof for the `countToB` program defined in the paper, execute the following commands:

- `stack repl examples/ExampleHoare.hs --ghci-options -iexamples`
- Once in the REPL mode, evaluate `putStrLn $ pr proof`
