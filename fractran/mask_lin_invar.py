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


def min_vals(rule: Rule) -> list[int]:
    """Min values required in order to apply this rule."""
    return [max(0, -x) for x in rule.array]

def dot(xs, ys):
    assert len(xs) == len(ys), (xs, ys)
    return z3.Sum([v * c for v, c in zip(xs, ys)])

def decide(prog: Program, start_state: State) -> DecideResult:
    """
    Proves non-halting for a Fractran program given in vector form.

    Args:
        transitions: List of vectors representing the change in state (Delta).
        start_index: The index of the variable representing the start state (usually 'a'=0).
    """
    num_rules = prog.num_rules()
    num_vars = prog.num_registers()
    requirements = [min_vals(trans) for trans in prog.rules]

    # 1. Identify 'Safe' Variables
    # A variable is safe if it ALONE guarantees a rule triggers (req has only 1 non-zero entry).
    # We also require that it only appears once in that denominator (25/3 is good, but 25/9 is not).
    safe_indices = set()
    for req in requirements:
        active_vars = [(i,x) for i, x in enumerate(req) if x > 0]
        if len(active_vars) == 1 and active_vars[0][1] == 1:
            safe_indices.add(active_vars[0][0])

    # Find S1 (Floor) and S2 (Ceiling) where S2 drops ONLY on 'Violator', protected by 'Protector'.
    for v_idx in range(num_rules):       # Violator Rule Index
        for p_idx in range(v_idx):       # Protector Rule Index (Must have higher priority)

            # Check Compatibility: P must require exactly one variable that V does not.
            # This missing variable is the "Gate" (it must be 0 for V to run).
            # (Note: if P requires 2+ variables that V does not, we don't know which one failed!)
            gate_vars = [k for k in range(num_vars) if requirements[p_idx][k] > 0 and requirements[v_idx][k] == 0]
            if len(gate_vars) != 1:
                continue # P cannot protect V
            gate_var, = gate_vars
            # We currently only support gate variables where we know that they are 0 if they get past the protector.
            if requirements[p_idx][gate_var] != 1:
                continue

            s = z3.Solver()
            S1 = [z3.Int(f"S1_{i}") for i in range(num_vars)]
            S2 = [z3.Int(f"S2_{i}") for i in range(num_vars)]

            # S1 Constraints (The Floor)
            # S1 never decreases and starts >= 1
            # Therefore, at any point in the future it will have value >= 1
            s.add(dot(S1, start_state.array) >= 1)
            for i in range(num_rules):
                s.add(dot(S1, prog.rules[i].array) >= 0) # S1 never decreases

            # S2 Constraints (The Ceiling)
            # S2 is also always >= 1, but the reasoning is slightly more complicated.
            # It starts >= 1 and does not decrease except for one (violator) rule.
            # After that violator rule applies, we show that S2 >= S1 >= 1.
            s.add(dot(S2, start_state.array) >= 1)
            # S2 is non-decreasing on all rules except the violator rule.
            for i in range(num_rules):
                if i != v_idx:  # No constraint on the "violator" rule
                    s.add(dot(S2, prog.rules[i].array) >= 0) # Others non-decreasing

            # When S2 > 0, it is impossible for the program to halt because it must
            # have positive values in some "safe" registers that guarantee that a
            # rule will always apply.
            # We guarantee this by requiring all weights to be <= 0 for unsafe registers
            # which means that if S2 > 0, at least one safe register must be positive.
            for i in range(num_vars):
                if i not in safe_indices:
                    s.add(S2[i] <= 0)

            # Constraints for when violator rule applies.
            # The goal here is to prove that after the violator rule applies, S2 >= S1.
            # In order to prove this we require:
            #   A) S2 >= S1 before the violator rule applies (in other words, all components
            #      of S2 >= S1 except for the gate_var (which will be 0 when violator gate applies)).
            #   B) S2 . x >= S1 . x where x = requiremens[v] +

            # The Gating Constraint (S2 must stay >= S1 after the drop)
            # We enforce S2 >= S1 on all vars except the gate_var (which is 0).
            for i in range(num_vars):
                if i != gate_var:
                    s.add(S2[i] >= S1[i])

            # We require that S2 >= S1 directly after applying the violator rule.
            # Here we consider the min state after (`min_after`).
            # If it is larger in any register other than `gate_var` (which is 0)
            # then the above check ensures that will only make S2 - S1 bigger.
            min_before = requirements[v_idx]
            min_after = [min_before[i] + prog.rules[v_idx].array[i]
                         for i in range(num_vars)]
            S1_after = dot(S1, min_after)
            S2_after = dot(S2, min_after)
            s.add(S2_after >= S1_after)

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
