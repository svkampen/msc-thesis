# Abstract Rewriting in Lean

## Overview

This Lean project contains the foundations of abstract rewriting theory in Lean,
along with a formalization of a recent result, namely the completeness of two-label
DCR for proving confluence of countable systems.

The structure of the project is as follows:

  - Thesis/ARS: definitions of ARS, sub-ARS
  - Thesis/BasicProperties: confluence, normalization, theorems linking these
  - Thesis/Cofinality: cofinal set, cofinal reduction, cofinality property + theorems
  - Thesis/DecreasingDiagrams: DCR, locally decreasing, proof of completeness of DCR for confluence of countable systems
  - Thesis/InfReductionSeq: expansion of infinite (reflexive-)transitive reduction sequences
  - Thesis/Misc: miscellaneous definitions and notation
  - Thesis/Multiset: Dershowitz-Manna order, well-foundedness
  - Thesis/Newman: three proofs of Newman's lemma
  - Thesis/ReductionSeq: finite and infinite reduction sequences, inductive and functional flavors
  - Thesis/TwoLabel: proof of completeness of DCR with two labels for confluence of countable systems
  - Thesis/WCRWNInc: proof of WCR and WN and Inc implies SN

## Getting started

If you are using Lean in VSCode, you should just be able to open the project and the extension should resolve everything.

## Leandoc
There is automatically generated API documentation for this project, available at https://svkampen.github.io/msc-thesis/

## More information
For more information, refer to the written thesis about this project [here](https://segfault.party/msc-thesis.pdf).
