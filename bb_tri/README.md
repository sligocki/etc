# Busy Beaver Trivalent Tree Search Tool

A search tool and simulator for Busy Beaver Turing Machines operating on an infinite trivalent tree.

## Tape Geometry

Unlike traditional Busy Beaver challenges where the tape is a 1D line with `L` (Left) and `R` (Right) moves, this tape is an infinite acyclic graph where every node has degree 3. 

The edges from every node are uniquely colored **Red (R)**, **Green (G)**, and **Blue (B)**. The TM navigates the tape by moving along these colored edges. Moving along the same color you just arrived on takes you back to your previous node.

The current position of the machine is represented as the shortest path from the origin, e.g., `RB` (move Red, then move Blue).

## TM Format

This project uses a modified version of the [Standard Text Format](https://wiki.bbchallenge.org/wiki/Turing_machine#Standard_text_format). 

Instead of `L` and `R` for directions, transitions use `R`, `G`, and `B`.

For example, `1RA0GB_1GA0RZ`:
- **State A**:
  - Read `0`: Write `1`, Move `R` (Red), goto State `A`
  - Read `1`: Write `0`, Move `G` (Green), goto State `B`
- **State B**:
  - Read `0`: Write `1`, Move `G` (Green), goto State `A`
  - Read `1`: Write `0`, Move `R` (Red), goto State `Z` (Halt)

## Building

You will need Rust and Cargo installed.
```bash
cargo build --release
```

## Usage

The CLI exposes two primary commands: `simulate` and `enumerate`.

### Simulate

Simulate a specific TM string up to a step limit:

```bash
./target/release/bb_tri simulate 1RA0GB_1GA0RZ --steps 10000
```
This will print `Halt <steps> <score>`, `Unknown`, or `Hit undefined transition`.

### Enumerate

Enumerate all TMs for a given number of states and symbols using Tree Normal Form (TNF) to avoid generating isomorphic machines. It cleanly breaks color symmetry by enforcing that the first newly explored edges must follow the sequence `R` -> `G` -> `B`.

```bash
./target/release/bb_tri enumerate <STATES> --symbols <SYMBOLS> --steps <LIMIT>
```

**Example:** Enumerate all 2-state, 2-symbol machines up to 1000 steps.
```bash
./target/release/bb_tri enumerate 2 --symbols 2 --steps 1000
```

By default, `enumerate` will output progress and a summary. You can use the `--output` (`-o`) flag to save all generated TMs and their results to a file.

```bash
./target/release/bb_tri enumerate 3 --steps 1000 --output out.txt
```
