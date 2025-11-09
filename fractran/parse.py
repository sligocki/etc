from collections import Counter

import numpy as np

from base import State, Program


_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
def prime_factor(n: int) -> State:
  counts = Counter[int]()
  i = 0
  while n > 1:
    p = _primes[i]
    if n % p == 0:
      n //= p
      counts[i] += 1
    else:
      i += 1
  return np.array([counts[i] for i in range(max(counts.keys(), default=0) + 1)])


def normalize_program(prog: Program) -> None:
  """Make sure all rules have the same size"""
  size = max(rule.size for rule in prog)
  for rule in prog:
    rule.resize(size)

def parse_program(prog_str: str) -> Program:
  rule_strs = prog_str.removeprefix("[").removesuffix("]").split(",")
  fracs = []
  width = 0
  for rule_str in rule_strs:
    p, q = rule_str.split("/")
    top = prime_factor(int(p))
    bot = prime_factor(int(q))
    fracs.append((top, bot))
    width = max(width, top.size, bot.size)
  prog = []
  for (top, bot) in fracs:
    top.resize(width)
    bot.resize(width)
    prog.append(top - bot)
  return prog
