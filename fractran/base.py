from dataclasses import dataclass
from fractions import Fraction

import numpy as np

from primes import prime_factor, factors_to_frac, factors_to_int


def fib_size(n: int) -> int:
  """Size of `n` when encoded using Fibinacci coding
    https://en.wikipedia.org/wiki/Fibonacci_coding
    1 -> "11", 2 -> "011", 3 -> "0011", 4 -> "1011", ..."""
  # Fib size increases by one at each fib number, starting from size 2 for 1.
  size, a, b = 1, 1, 1
  while b <= n:
    a, b = b, a+b
    size += 1
  return size

def make_array(vals, width: int = 0) -> np.ndarray:
  arr = np.array(vals, dtype=int)
  if width:
    assert width >= arr.size, (arr, width)
    arr.resize(width)
  return arr

@dataclass(frozen=True)
class Rule:
  array: np.ndarray

  @staticmethod
  def from_ratio(top, bot, num_registers: int) -> Rule:
    return Rule(make_array(top, num_registers) - make_array(bot, num_registers))

  def __str__(self) -> str:
    return str(self.array)
  def as_fraction(self) -> Fraction:
    return factors_to_frac(list(self.array))

  def cost(self) -> int:
    """Measure size of rule in number of prime factors of both num and denom."""
    return np.abs(self.array).sum()
  def bit_size(self) -> int:
    """Measure size of rule in bits using Fibinacci coding."""
    top, bot = self.as_fraction().as_integer_ratio()
    return fib_size(top) + fib_size(bot)
  def num_registers(self) -> int:
    return self.array.size

@dataclass(frozen=True)
class State:
  array: np.ndarray

  @staticmethod
  def from_int(val: int, num_registers: int) -> State:
    factors = prime_factor(val)
    return State(make_array(factors, num_registers))

  def try_apply(self, rule: Rule) -> State | None:
    new_array = self.array + rule.array
    if np.all(new_array >= 0):
      return State(new_array)
    else:
      return None

  def __str__(self) -> str:
    return str(self.array)
  def as_int(self) -> int:
    return factors_to_int(list(self.array))

@dataclass(frozen=True)
class Program:
  rules: list[Rule]

  def num_rules(self) -> int:
    return len(self.rules)
  def num_registers(self) -> int:
    return self.rules[0].num_registers()
  def cost(self) -> int:
    """Measure size of program in number of prime factors of all fractions + num rules."""
    return self.num_rules() + sum(rule.cost() for rule in self.rules)
  def bit_size(self) -> int:
    """Measure size of program in bits using a prefix-free encoding using Fibinacci coding."""
    return fib_size(self.num_rules()) + sum(rule.bit_size() for rule in self.rules)

  def step(self, state: State) -> tuple[State | None, int]:
    for rule_num, rule in enumerate(self.rules):
      if (new_state := state.try_apply(rule)):
        return (new_state, rule_num)
    # We treat "halt" as applying rule after last rule (max_rule_num+1).
    return (None, self.num_rules())

  def __str__(self) -> str:
    return "\n".join(str(rule) for rule in self.rules)
  def as_fractions(self) -> list[Fraction]:
    return [rule.as_fraction() for rule in self.rules]
  def fractions_str(self) -> str:
    return "[" + ", ".join(str(frac) for frac in self.as_fractions()) + "]"
