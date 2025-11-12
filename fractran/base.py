from dataclasses import dataclass

import numpy as np

type State = np.array
type Rule = np.array

def rule_size(rule: Rule) -> int:
  return np.abs(rule).sum()

@dataclass(frozen=True)
class Program:
  rules: list[Rule]

  def num_rules(self) -> int:
    return len(self.rules)
  def num_vars(self) -> int:
    return self.rules[0].size
  def size(self) -> int:
    return self.num_rules() + sum(rule_size(rule) for rule in self.rules)

  def __iter__(self):
    yield from self.rules

  def __str__(self) -> str:
    return "\n".join(str(rule) for rule in self.rules)
