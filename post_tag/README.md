# Post Tag System Busy Beaver ($BB_{PT}$)

This project is a high-performance Rust toolkit for searching for the Busy Beaver function for Post Tag Systems, denoted as $BB_{PT}(v, S)$.

## Mathematical Formalization

A Post Tag System in our Busy Beaver domain is parameterized by $(v, S)$:
*   **$v \ge 1$**: The deletion number (the number of symbols consumed from the front of the tape per step).
*   **$S \ge 1$**: The total size budget of the system.

### System Architecture
For a given $(v, S)$, a valid tag system consists of:
*   **Alphabet**: $\Sigma = \{0, 1, \dots, n-1\}$, where the number of symbols $n$ is dynamically chosen by the system.
*   **Productions**: Exactly $n$ rules, where each rule maps a symbol $i \in \Sigma$ to a string $w_i \in \Sigma^*$.

### Size Constraint
The total size of the system must exactly equal $S$:
$$S = n + \sum_{i=0}^{n-1} |w_i|$$
*This ensures that every symbol in the alphabet costs at least 1, allowing for empty-string productions ($|w_i| = 0$) without breaking the size budget.*

### Execution & Halting
*   **Initial Tape**: The system always starts at Step 0 with the tape $0^v$ (the symbol `0` repeated $v$ times). Because the first step always consumes $v$ symbols, the system effectively defines its true initial starting tape using $w_0$.
*   **Step Mechanic**: If the tape length is $\ge v$, read the first symbol $x$. Delete the first $v$ symbols from the tape, and append $w_x$ to the end of the tape.
*   **Halting**: The system halts if and only if the length of the tape becomes strictly less than $v$. We do not require a specific "halt" symbol.

### Metrics
We track two metrics for halting systems:
1.  **Time (Steps)**: The maximum number of steps executed before halting. This is the primary BB metric, analogous to the `S` or `Shift` function.
2.  **Space (Max Tape Length)**: The maximum length the tape reaches at any point during a halting execution. This is a secondary metric of interest.

---

## Toolkit Usage

The codebase is split into two primary binaries:

### 1. `enum` (The Exhaustive Searcher)
Generates and simulates all valid tag systems fitting exactly within size $S$.

**Usage:**
```bash
cargo run --release --bin enum -- <max_S>
```

**Optional Flags:**
*   `--del <v>`: Specify the deletion number (defaults to `2`).
*   `--max-steps <STEPS>`: Limit the number of steps before a system is classified as a "Holdout" (defaults to `1,000,000`).

**Example:** Search up to $S=5$ with deletion number 2:
```bash
cargo run --release --bin enum -- 5 --del 2
```

### 2. `sim` (The Single System Simulator)
Quickly simulates a specific, manually-defined tag system.

**Usage:**
```bash
cargo run --release --bin sim -- "<rule_string>"
```

**Rule String Format:**
Provide rules as a comma-separated list formatted like `LHS->RHS`. Empty strings are denoted by `eps`.
*Example: `0->011, 1->eps`*

**Example:** Simulate the $S=5$ champion:
```bash
cargo run --release --bin sim -- "0->011, 1->eps"
```
