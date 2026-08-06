# GenRec Proofs

This directory contains formalizations of General Recursive Functions (GRF) and Primitive Recursive Functions (PRF) in [Lean 4](https://leanprover.github.io/), written to verify the behavior of holdout programs discovered by the main `gen_rec` project.

## Overview

While the Rust codebase implements fast evaluation and algebraic heuristics (like `ClosedForm` extraction) to classify the behavior of most GRFs, some specific M(PRF) "holdout" expressions resist automated heuristics and evaluate too slowly to simulate to completion.

This Lean 4 project is designed to mathematically prove whether these specific holdouts terminate or diverge.

## Structure

* `GenRec/Syntax.lean`: Defines the `PRF k` inductive type, strictly modeling arity for atoms (Zero, Successor, Projection) and combinators (Composition, Primitive Recursion).
* `GenRec/Semantics.lean`: Formalizes the standard evaluation semantics of these functions.
* `GenRec/Holdouts13.lean` & `GenRec/Holdouts14.lean`: Automatically translated theorem statements for the size-13 and size-14 holdouts asserting their divergence.
* `scripts/grl_to_lean.py`: Python script used to automatically translate `.grl` holdout files into Lean 4 `PRF` definitions and theorems.

## Building and Checking

This project uses `lake`, the standard package manager for Lean 4. To build the project and check the proofs:

```bash
lake build
```
