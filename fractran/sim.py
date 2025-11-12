import argparse

import numpy as np

from base import State, Program
from parse import parse_program, prime_factor

def step(prog: Program, state: State) -> tuple[State | None, int]:
  for rule_num, rule in enumerate(prog):
    new_state = state + rule
    if np.all(new_state >= 0):
      return (new_state, rule_num)
  return (None, len(prog))

def run(prog: Program, state: State, num_steps: int) -> State | None:
  cur = state
  while cur is not None and num_steps > 0:
    cur, _ = step(prog, cur)
    num_steps -= 1
  return cur


def sim(prog: Program, state: State, print_rule: int) -> None:
  print("Program:", prog)
  print("Start:", state)

  num_steps = 0
  while state is not None:
    next_state, rule_num = step(prog, state)
    num_steps += 1
    if rule_num >= print_rule:
      print(f"{num_steps:7_d}:  r{rule_num}:  {state}  ->  {next_state}")
    state = next_state


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("program")
  parser.add_argument("print_rule", type=int, nargs="?", default=0)
  parser.add_argument("--start", type=int, default=2)
  args = parser.parse_args()

  prog = parse_program(args.program)
  start = prime_factor(args.start)
  start.resize(prog[0].size)

  sim(prog, start, args.print_rule)

if __name__ == "__main__":
  main()