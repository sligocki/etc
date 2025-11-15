#!/usr/bin/env python3
# Simulate all programs in a file for some number of steps and report if they halted.

import argparse
from dataclasses import dataclass
from pathlib import Path
import sys
import time

from base import State, Program
from parse import enum_programs


@dataclass(frozen=True)
class SimResult:
  halted: bool
  num_steps: int
  final_state: State | None


def run(prog: Program, start: State, max_steps: int) -> SimResult:
  state : State | None = start
  num_steps = 0
  while state is not None and num_steps < max_steps:
    prev_state = state
    state, _ = prog.step(state)
    num_steps += 1
  return SimResult(halted=(state is None), num_steps=num_steps, final_state=prev_state)


class OutputWriter:
  def __init__(self, outfile):
    self.outfile = outfile
    self.num_halt = 0
    self.num_total = 0
    self.max_halt_time = 0

  def write(self, prog: Program, result: SimResult) -> None:
    if result.halted:
      status = "HALT"
      self.num_halt += 1
      self.max_halt_time = max(self.max_halt_time, result.num_steps)
    else:
      status = "UNKNOWN"
    self.num_total += 1
    self.outfile.write(f"{prog.fractions_str()}\t{status}\t{result.num_steps}\n")


def main() -> None:
  parser = argparse.ArgumentParser()
  parser.add_argument("infile", type=Path)
  parser.add_argument("outfile", type=Path)
  parser.add_argument("max_steps", type=int)
  parser.add_argument("--print-sec", type=float, default="60")
  args = parser.parse_args()

  with open(args.outfile, "w") as outfile:
    writer = OutputWriter(outfile)
    print_time = time.time() + args.print_sec
    for prog in enum_programs(args.infile):
      start = State.from_int(2, prog.num_registers())
      result = run(prog, start, args.max_steps)
      writer.write(prog, result)
      if time.time() >= print_time:
        print(f"...  Total: {writer.num_total:_d}  Halted: {writer.num_halt:_d} ({writer.num_halt/writer.num_total:.0%})  Max Halt Time: {writer.max_halt_time:_d}  ({time.process_time():_f}s)")
        print_time = time.time() + args.print_sec

  print(f"Finished:  Total: {writer.num_total:_d}  Halted: {writer.num_halt:_d} ({writer.num_halt/writer.num_total:.0%})  Max Halt Time: {writer.max_halt_time:_d}  ({time.process_time():_f}s)")

if __name__ == "__main__":
  main()
