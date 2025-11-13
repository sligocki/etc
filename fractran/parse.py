from pathlib import Path

import numpy as np

from base import Rule, Program
from primes import prime_factor


def parse_fractions(prog_str: str) -> Program:
  rule_strs = prog_str.strip().removeprefix("[").removesuffix("]").split(",")
  fracs = []
  num_reg = 0
  for rule_str in rule_strs:
    p, q = rule_str.split("/")
    top = prime_factor(int(p))
    bot = prime_factor(int(q))
    fracs.append((top, bot))
    num_reg = max(num_reg, len(top), len(bot))
  prog = []
  for (top, bot) in fracs:
    prog.append(Rule.from_ratio(top, bot, num_reg))
  return Program(prog)

def parse_vectors(prog_str: str) -> Program:
  prog = []
  for line in prog_str.split("\n"):
    line = line.strip().removeprefix("[").removesuffix("]")
    if line:
      prog.append(Rule(np.fromstring(line, dtype=int, sep=" ")))
  return Program(prog)


def load_program(prog_or_filename: str | Path) -> Program:
  if Path(prog_or_filename).exists():
    with open(prog_or_filename, "r") as f:
      prog_str = f.read()
  else:
    prog_str = str(prog_or_filename)

  if "/" in prog_str:
    return parse_fractions(prog_str)
  else:
    return parse_vectors(prog_str)
