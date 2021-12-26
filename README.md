# Tutorial implementation of Hoare logic in Haskell

This is the source code repository for my paper `Tutorial implementation of Hoare logic in Haskell`. In the `src` folder you will find:

- `Common.hs`, `PrettyPrinter.hs` - Various utility functions
- `Gentzen.hs` - Implementation of Propositional calculus
- `TNT.hs` - Implementation of Typographical Number Theory
- `Hoare.hs` - Implementation of Hoare logic (on top of Propositional calculus + Number theory)
- `Imp.hs` - Implementation of a simple imperative programming language (the commands correspond to the rules of Hoare logic)

The folder `paper` contains the source code of the paper. The built paper can be downloaded from https://arxiv.org/abs/2101.11320.

See it in action on my mobile phone on [this Tweet](https://twitter.com/BSitnikovski/status/1386738126677291012)

## Prerequisites

Make sure you have the [Haskell Tool Stack](https://haskellstack.org/) installed, or Hugs.

## Running the examples

Check the files in the `examples` folder - each implementation of the system has a corresponding example file.

For instance, to run the proof for the `countToB` program defined in the paper, execute the following commands:

- `stack repl examples/ExampleHoare.hs --ghci-options -iexamples --ghci-options -isrc`
- Once in the REPL mode, evaluate `putStrLn $ pr proof`

For hugs, while in the `src` folder, run `hugs -F"cpphs-hugs --noline -D__HUGS__" ../examples/ExampleHoare.hs`

Copyright 2021, Boro Sitnikovski. All rights reserved.
