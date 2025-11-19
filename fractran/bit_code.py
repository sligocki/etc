# Functions for working with prefix-free binary encodings of Fractran programs.

from fractions import Fraction

from primes import factors_to_int
from base import Rule, Program

# First we have enocodings based on Fibonacci coding which encodes all positive
# numbers into prefix-free binary strings:
#   https://en.wikipedia.org/wiki/Fibonacci_coding
#   1 -> "11", 2 -> "011", 3 -> "0011", 4 -> "1011", 5 -> "00011",
#   6 -> "10011", 7 -> "01011", 8 -> "000011", 9 -> "100011", 10 -> "010011", ...

def fib_size(n: int) -> int:
  """Size of `n ≥ 1` when encoded using Fibinacci coding."""
  assert n >= 1, n
  # Fib size increases by one at each fib number, starting from size 2 for 1.
  size, a, b = 1, 1, 1
  while b <= n:
    a, b = b, a+b
    size += 1
  return size

# All codes use the following high level encoding: fib_code(num_rules) + code(rule[0]) + ... + code(rule[n-1])
# They differ in how they code each rule:

# Fib code 1:  Rule p/q  ->  fib_code(p) + fib_code(q)
def fib_code_size(prog: Program) -> int:
  def rule_size(rule: Rule) -> int:
    top, bot = rule.as_fraction().as_integer_ratio()
    return fib_size(top) + fib_size(bot)
  return fib_size(prog.num_rules()) + sum(rule_size(rule) for rule in prog.rules)

# Fib code 2:  Rule [a, 0, -c, d] ->  fib_code(2^{2a-1} 3^0 5^{2c} 7^{2d-1})
def int_to_nat(n: int) -> int:
   """Bijection from all integers to non-negative integers in this order:
   [0, 1, -1, 2, -2, 3, -3, ...]"""
   if n > 0:
      return 2*n - 1
   else:
      return -2*n

def fib_code2_size(prog: Program) -> int:
  def rule_size(rule: Rule) -> int:
    nat_vec = [int_to_nat(n) for n in rule.array]
    int_code = factors_to_int(nat_vec)
    return fib_size(int_code)
  return fib_size(prog.num_rules()) + sum(rule_size(rule) for rule in prog.rules)

# Next we have continued faction encoding where we encode a fraction based on its
# continued fraction.
def cont_frac(frac: Fraction) -> list[int]:
  ret = []
  while True:
    k, r = divmod(frac, 1)
    ret.append(k)
    if r == 0:
      return ret
    frac = 1/r

def cf_code_size_frac(frac: Fraction) -> int:
  cf = cont_frac(frac)
  # Continued fractions are integer lists constrained by:
  #   cf[0] ≥ 0, cf[i] ≥ 1, cf[-1] ≥ 2
  # So we can encode them as:
  #   fib_code(len(cf)) + fib_code(cf[0]+1) + fib_code(cf[1]) + ... fib_code(cf[-1]-1)
  # For alternative rep, see: https://stackoverflow.com/a/78345556/68736
  cf[0] += 1
  cf[-1] -= 1
  return fib_size(len(cf)) + sum(fib_size(x) for x in cf)

def cf_code_size(prog: Program) -> int:
  def rule_size(rule: Rule) -> int:
    frac = rule.as_fraction()
    return cf_code_size_frac(frac)
  return fib_size(prog.num_rules()) + sum(rule_size(rule) for rule in prog.rules)
