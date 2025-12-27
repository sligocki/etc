#!/usr/bin/env python3
# Simulate all programs in a file for some number of steps and report if they halted.

import argparse
from dataclasses import dataclass
from pathlib import Path
import time

from base import State, Program
from mask_lin_invar import decide, DecideResult
from parse import enum_programs

class OutputWriter:
  def __init__(self, outfile):
    self.outfile = outfile
    self.num_inf = 0
    self.num_total = 0

  def write(self, prog: Program, result: DecideResult) -> None:
    if result.infinite:
      self.outfile.write(f"{prog.fractions_str()}\tINF\t{result.num_rules},{result.protector_rule},{result.violator_rule},{result.gate_register}\t{result.weights}\n")
      self.num_inf += 1
    else:
      self.outfile.write(f"{prog.fractions_str()}\tUNKNOWN\n")
    self.num_total += 1


def main() -> None:
  parser = argparse.ArgumentParser()
  parser.add_argument("infile", type=Path)
  parser.add_argument("outfile", type=Path)
  parser.add_argument("--init-steps", type=int, default=100)
  parser.add_argument("--print-sec", type=float, default="60")
  args = parser.parse_args()

  with open(args.outfile, "w") as outfile:
    writer = OutputWriter(outfile)
    print_time = time.time() + args.print_sec
    for prog in enum_programs(args.infile):
      result = decide(prog, args.init_steps)
      writer.write(prog, result)
      if time.time() >= print_time:
        print(f"...  Total: {writer.num_total:_d}  Inf: {writer.num_inf:_d} ({writer.num_inf/writer.num_total:.0%})  ({time.process_time():_f}s)")
        print_time = time.time() + args.print_sec

  print(f"Finished:  Total: {writer.num_total:_d}  Inf: {writer.num_inf:_d} ({writer.num_inf/writer.num_total:.0%})  ({time.process_time():_f}s)")

if __name__ == "__main__":
  main()
