#!/usr/bin/env python3

import argparse
from dataclasses import dataclass

import z3

from base import State, Rule, Program
from parse import load_program
from show import print_program


@dataclass(frozen=True)
class DecideResult:
  infinite: bool
  weights: list[list[int]]
  gate_rule: int|None = None
  violator_rule: int|None = None


def req_of(rule: Rule) -> list[int]:
    return [max(0, -x) for x in rule.array]

def decide(prog: Program, start_state: State) -> DecideResult:
    """
    Proves non-halting for a Fractran program given in vector form.

    Args:
        transitions: List of vectors representing the change in state (Delta).
        start_index: The index of the variable representing the start state (usually 'a'=0).
    """
    num_rules = prog.num_rules()
    num_vars = prog.num_registers()
    requirements = [req_of(trans) for trans in prog.rules]

    # 1. Identify 'Safe' Variables
    # A variable is safe if it ALONE guarantees a rule triggers (req has only 1 non-zero entry).
    # We also require that it only appears once in that denominator (25/3 is good, but 25/9 is not).
    safe_indices = set()
    for req in requirements:
        active_vars = [(i,x) for i, x in enumerate(req) if x > 0]
        if len(active_vars) == 1 and active_vars[0][1] == 1:
            safe_indices.add(active_vars[0][0])

    # Z3 Setup
    s = z3.Solver()

    # Helper: Dot product for Z3 variables and integer list
    def dot(z3_vars, int_vec):
        return z3.Sum([v * c for v, c in zip(z3_vars, int_vec)])

    # --- STRATEGY 1: Simple Linear Invariant ---
    # Find W where W . Delta >= 0 for all rules.
    W = [z3.Int(f"W_{i}") for i in range(num_vars)]

    # C1: Start state > 0
    s.add(dot(W, start_state.array) > 0)

    # C2: Non-decreasing for all rules
    for i in range(num_rules):
        s.add(dot(W, prog.rules[i].array) >= 0)

    # C3: Halting Logic (Only safe vars can be positive)
    for i in range(num_vars):
        if i not in safe_indices:
            s.add(W[i] <= 0)

    if s.check() == z3.sat:
        return DecideResult(True, [[s.model()[w].as_long() for w in W]])

    # --- STRATEGY 2: Priority-Gated Invariant ---
    # Find S1 (Floor) and S2 (Ceiling) where S2 drops ONLY on 'Violator', protected by 'Protector'.

    for v_idx in range(num_rules):       # Violator Rule Index
        for p_idx in range(v_idx):       # Protector Rule Index (Must have higher priority)

            # Check Compatibility: P must require a variable that V does not.
            # This missing variable is the "Gate" (it must be 0 for V to run).
            gate_vars = [k for k in range(num_vars) if requirements[p_idx][k] > 0 and requirements[v_idx][k] == 0]
            if not gate_vars:
                continue # P cannot protect V

            gate_var = gate_vars[0] # Use the first valid gate variable

            s.reset()
            S1 = [z3.Int(f"S1_{i}") for i in range(num_vars)]
            S2 = [z3.Int(f"S2_{i}") for i in range(num_vars)]

            # S1 Constraints (The Floor)
            s.add(dot(S1, start_state.array) > 0)
            for i in range(num_rules):
                s.add(dot(S1, prog.rules[i].array) >= 0) # S1 never decreases

            # S2 Constraints (The Ceiling)
            s.add(dot(S2, start_state.array) > 0)
            for i in range(num_rules):
                if i != v_idx:  # No constraint on the "violator" rule
                    s.add(dot(S2, prog.rules[i].array) >= 0) # Others non-decreasing

            # Halting Logic for S2 (Dead ends must be <= 0)
            for i in range(num_vars):
                if i not in safe_indices:
                    s.add(S2[i] <= 0)

            # The Gating Constraint (S2 must stay >= S1 after the drop)
            # We enforce S2 >= S1 on all vars except the gate_var (which is 0).
            for i in range(num_vars):
                if i != gate_var:
                    s.add(S2[i] >= S1[i])

            # The Buffer: D . req_v >= |Drop|
            # (S2 - S1) . req_v >= -(S2 . delta_v)
            diff = [S2[i] - S1[i] for i in range(num_vars)]
            drop = -dot(S2, prog.rules[v_idx].array)
            buffer = dot(diff, requirements[v_idx])
            s.add(buffer >= drop)

            if s.check() == z3.sat:
                m = s.model()
                S1 = [m[v].as_long() for v in S1]
                S2 = [m[v].as_long() for v in S2]
                return DecideResult(True, [S1, S2], p_idx, v_idx)

    return DecideResult(False, [])


def main() -> None:
  parser = argparse.ArgumentParser()
  parser.add_argument("program")
  parser.add_argument("--start", type=int, default=2)
  args = parser.parse_args()

  prog = load_program(args.program)
  start = State.from_int(args.start, prog.num_registers())

  print_program(prog)
  print()

  result = decide(prog, start)
  if result.infinite:
      print("Success:", result.gate_rule, result.violator_rule, result.weights)
  else:
      print("Failure")

if __name__ == "__main__":
  main()
