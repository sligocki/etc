#!/usr/bin/env python3

import argparse

from base import Program
from parse import load_program

def print_program(prog: Program):
  print(f"Program cost: {prog.cost()}")
  print(prog.fractions_str())
  print()
  print(prog)

def latex_str(prog: Program) -> str:
  def cell_str(cell: int) -> str:
    return f"{cell:5d}"

  rows = []
  for rule in prog.rules:
    rows.append(" & ".join(cell_str(cell) for cell in rule.array))
  return r"\begin{bmatrix}" + "\n" + " \\\\\n".join(rows) + "\n" + r"\end{bmatrix}"


def main() -> None:
  parser = argparse.ArgumentParser()
  parser.add_argument("programs", nargs="+")
  parser.add_argument("--latex", action="store_true")
  args = parser.parse_args()

  for arg in args.programs:
    prog = load_program(arg)
    if args.latex:
      print(latex_str(prog))
    else:
      print_program(prog)
    print()

if __name__ == "__main__":
  main()
