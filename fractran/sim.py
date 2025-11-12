import argparse

from base import State, Program
from parse import load_program


def sim(prog: Program, in_state: State, print_rule: int) -> None:
  print(f"Program cost: {prog.cost()}")
  print(prog.fractions_str())
  print()
  print(prog)
  print()
  print("Start:", in_state)
  print()

  num_steps = 0
  state : State | None = in_state
  while state is not None:
    next_state, rule_num = prog.step(state)
    num_steps += 1
    if rule_num >= print_rule:
      print(f"{num_steps:7_d}:  r{rule_num}:  {state}  ->  {next_state}")
    state = next_state


def main() -> None:
  parser = argparse.ArgumentParser()
  parser.add_argument("program")
  parser.add_argument("print_rule", type=int, nargs="?", default=0)
  parser.add_argument("--start", type=int, default=2)
  args = parser.parse_args()

  prog = load_program(args.program)
  start = State.from_int(args.start, prog.num_registers())

  sim(prog, start, args.print_rule)

if __name__ == "__main__":
  main()
