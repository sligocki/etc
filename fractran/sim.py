#!/usr/bin/env python3

import argparse
import string

from base import State, Program
from parse import load_program
from show import print_program


RULE_CHARS = string.ascii_uppercase

def sim(prog: Program, start: State,
        print_rule: int, print_transcript: bool) -> None:
  num_steps = 0
  state : State | None = start
  transcript = []
  while state is not None:
    next_state, rule_num = prog.step(state)
    num_steps += 1
    if rule_num >= print_rule:
      if print_transcript:
        print("Transitions:", "".join(transcript))
      print(f"{num_steps:7_d}:  r{rule_num}:  {state}  ->  {next_state}")
      transcript = []
    transcript.append(RULE_CHARS[rule_num])
    state = next_state


def main() -> None:
  parser = argparse.ArgumentParser()
  parser.add_argument("program")
  parser.add_argument("print_rule", type=int, nargs="?", default=0)
  parser.add_argument("--start", type=int, default=2)
  parser.add_argument("--transcript", "-t", action="store_true")
  args = parser.parse_args()

  prog = load_program(args.program)
  start = State.from_int(args.start, prog.num_registers())

  print_program(prog)
  print()
  print("Start:", start)
  print()

  sim(prog, start, args.print_rule, args.transcript)

if __name__ == "__main__":
  main()
