from dataclasses import dataclass

import numpy as np


def make_array(vals, width: int) -> np.ndarray:
  arr = np.array(vals, dtype=int)
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

  def cost(self) -> int:
    return np.abs(self.array).sum()
  def num_registers(self) -> int:
    return self.array.size

@dataclass(frozen=True)
class State:
  array: np.ndarray

  @staticmethod
  def from_seq(vals, num_registers: int) -> State:
    return State(make_array(vals, num_registers))

  def try_apply(self, rule: Rule) -> State | None:
    new_array = self.array + rule.array
    if np.all(new_array >= 0):
      return State(new_array)
    else:
      return None

  def __str__(self) -> str:
    return str(self.array)

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


  # def __iter__(self):
  #   yield from self.rules

  def __str__(self) -> str:
    return "\n".join(str(rule) for rule in self.rules)
