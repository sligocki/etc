import argparse

import numpy as np

from base import State, Program
from parse import parse_program, prime_factor

def step(prog: Program, state: State) -> State | None:
  for rule in prog:
    new_state = state + rule
    if np.all(new_state >= 0):
      return new_state
  return None

def run(prog: Program, state: State, num_steps: int) -> State | None:
  cur = state
  while cur is not None and num_steps > 0:
    cur = step(prog, cur)
    num_steps -= 1
  return cur


def sim(prog: Program, state: State) -> None:
  print("Program:", prog)
  print("Start:", state)

  num_steps = 0
  while state is not None:
    state = step(prog, state)
    num_steps += 1
    print(num_steps, state)


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("program")
  parser.add_argument("start", type=int)
  args = parser.parse_args()

  prog = parse_program(args.program)
  start = prime_factor(args.start)
  start.resize(prog[0].size)

  sim(prog, start)

if __name__ == "__main__":
  main()