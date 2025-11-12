from collections import Counter
from pathlib import Path

import numpy as np

from base import Rule, Program


_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
def prime_factor(n: int) -> list[int]:
  counts = Counter[int]()
  i = 0
  while n > 1:
    p = _primes[i]
    if n % p == 0:
      n //= p
      counts[i] += 1
    else:
      i += 1
  return [counts[i] for i in range(max(counts.keys(), default=0) + 1)]


def parse_fractions(prog_str: str) -> Program:
  rule_strs = prog_str.removeprefix("[").removesuffix("]").split(",")
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
