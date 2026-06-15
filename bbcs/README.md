# BBCS (Busy Beaver for CounterScript)

BBCS is a Rust enumerator and simulator that searches for "Busy Beaver" programs within a simple imperative language (CounterScript). The language consists only of increment, saturating decrement, and `while` loop instructions. The goal of the search is to find the halting program of a given length that produces the largest single counter value (the "score").

## Language Specification

The language features an infinite array of registers (`A`, `B`, `C`, etc.) initialized to `0`. There are only three instruction types:
- `Inc(X)` or `X++;`: Increment register `X` by 1.
- `Dec(X)` or `X--;`: Decrement register `X` by 1 (saturates at 0).
- `While(X) { ... }` or `while X { ... }`: Execute the inner block of instructions repeatedly as long as register `X` is strictly greater than `0`.

## Architecture

The project is structured to generate and evaluate all canonical programs of a specific length using parallel execution:
- **`enumerator.rs`**: Recursively generates canonical syntax trees, skipping symmetrical or uninteresting variants to drastically reduce the search space. Uses `rayon` to evaluate distinct program branches across multiple threads.
- **`simulator.rs`**: An execution engine that runs the generated programs up to a specified step limit.
- **Deciders**: The simulator employs several deciders that detect non-halting (infinite) behavior:
  - **Stationary Cycles**: The exact same program state is encountered at the same instruction pointer again.
  - **Translated Cycles**: The state strictly grows across iterations of a while loop.
  - **Symbolic Monotonic Cycles**: The loop can be statically proven to never decrease its condition variable.
  - **Sum Monotonic Cycles**: The total sum of the state never decreases across the loop iteration and there is evidence that some of that sum is always in the loop variable.

## Usage

You can run the enumerator via `cargo run`:

```bash
cargo run --release -- --length <LENGTH> --max-steps <MAX_STEPS> [--output <FILE>]
```

### Options

- `-l, --length <usize>`: The total length (AST size) of the programs to search.
- `-m, --max-steps <usize>`: Maximum steps the simulator should execute before giving up and returning a Timeout.
- `-o, --output <String>`: (Optional) Path to a file where simulation traces/results will be saved.

### Example

To search all programs of length 10, simulating each for up to 1,000 steps:

```bash
cargo run --release --bin bbcs -- -l 10 -m 1000
```

**Example Output:**
```
Streaming and simulating all canonical programs of length 10 with max steps 1000...
Completed in 800ms
--- Results ---
Total Programs: 1641576
Halted:         1449697
Timeouts:       3375
Inf (Stat):     130588
Inf (Trans):    43005
Inf (Symbolic): 4342
Inf (Sum):      10569
Max Score:      16
Max Steps:      57
Champion Code:  A++; A++; A++; A++; while A { A--; B++; B++; B++; B++; }
```

## Compilation

Build the project using standard cargo commands. Release mode is highly recommended due to the extremely large search space for lengths `> 10`.

```bash
cargo build --release
```
