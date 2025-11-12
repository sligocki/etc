#!/usr/bin/env python3

import argparse

from base import Program
from parse import load_program

def print_program(prog: Program):
  print(f"Program cost: {prog.cost()}")
  print(prog.fractions_str())
  print()
  print(prog)


def main() -> None:
  parser = argparse.ArgumentParser()
  parser.add_argument("programs", nargs="+")
  args = parser.parse_args()

  for arg in args.programs:
    prog = load_program(arg)
    print_program(prog)
    print()

if __name__ == "__main__":
  main()
