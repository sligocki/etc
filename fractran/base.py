from dataclasses import dataclass
from fractions import Fraction

import numpy as np

from primes import prime_factor, factors_to_frac, factors_to_int


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
    return np.abs(self.array).sum()
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
    return self.num_rules() + sum(rule.cost() for rule in self.rules)

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
