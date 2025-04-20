# Investigate how many gates are needed to compute Boolean functions.
# Using PLA model: https://en.wikipedia.org/wiki/Programmable_logic_array

from __future__ import annotations

import argparse
from collections.abc import Sequence
from dataclasses import dataclass
from enum import Enum
from functools import total_ordering
import itertools
import time
from typing import Iterator


# Frozen list type
type List[T] = tuple[T, ...]


@dataclass
class InputLead:
  index: int
  negate: bool

  def eval(self, input_vals : Sequence[bool]) -> bool:
    # Use XOR (^) to swap the value if self.negate is true.
    return input_vals[self.index] ^ self.negate

@dataclass
class AndGate:
  inputs: List[InputLead]

  def eval(self, input_vals : Sequence[bool]) -> bool:
    return all(i.eval(input_vals) for i in self.inputs)

@dataclass
class OrGate:
  inputs: List[int]

  def eval(self, input_vals : Sequence[bool]) -> bool:
    return any(input_vals[index] for index in self.inputs)

@dataclass
class Circuit:
  and_plane: List[AndGate]
  or_plane: List[OrGate]

  def eval(self, input_vals : Sequence[bool]) -> List[bool]:
    and_vals = tuple(g.eval(input_vals) for g in self.and_plane)
    return tuple(g.eval(and_vals) for g in self.or_plane)


def count_and_trans(and_plane: List[AndGate]) -> int:
  """Count # transistors needed in a collection of AND gates."""
  return sum(len(gate.inputs) for gate in and_plane)

def enum_and_gates(num_inputs: int) -> Iterator[AndGate]:
  # Enumerate all possible AND gates. An AND gate in PLA can require (for each input)
  # that it be 0, 1 or - (don't care). We use None for -.
  for config in itertools.product([None, False, True], repeat=num_inputs):
    inputs = []
    for index, negate in enumerate(config):
      if isinstance(negate, bool):
        inputs.append(InputLead(index, negate))
    # Ignore the empty AND gate
    if inputs:
      yield AndGate(tuple(inputs))

def enum_and_planes(num_inputs: int, num_ands: int) -> Iterator[List[AndGate]]:
  yield from itertools.combinations(enum_and_gates(num_inputs), num_ands)

def enum_or_planes(num_ands: int, num_outputs: int, num_trans: int) -> Iterator[List[OrGate]]:
  # A transistor could go at any combination of and gate and output wires.
  num_trans_locs = num_ands * num_outputs
  for locs in itertools.combinations(range(num_trans_locs), num_trans):
    or_inputs : list[list[int]] = [[] for _ in range(num_outputs)]
    for loc in locs:
      gate_num, and_num = divmod(loc, num_ands)
      or_inputs[gate_num].append(and_num)
    yield tuple(OrGate(tuple(inputs)) for inputs in or_inputs)

def enum_circuits(num_inputs: int, num_outputs: int,
                  num_ands: int, num_trans: int) -> Iterator[Circuit]:
  for and_plane in enum_and_planes(num_inputs, num_ands):
    num_or_trans = num_trans - count_and_trans(and_plane)
    if num_or_trans > 0:
      for or_plane in enum_or_planes(num_ands, num_outputs, num_or_trans):
        yield Circuit(and_plane, or_plane)


def main():
  n,m = 2,2
  for a in range(2**n + 1):
    for t in range((n+m)*a + 1):
      num_circuits = sum(1 for _ in enum_circuits(n,m,a,t))
      print(n,m,a,t,num_circuits)
main()