# Investigate how many gates are needed to compute Boolean functions.
# Using AIG (and-inverger graph) model:
#   https://en.wikipedia.org/wiki/And-inverter_graph

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


## Boolean function datatypes
# An n-input, m-output Boolean function (bf) should have 2^n rows with m booleans each.
#   * len(bf) = 2^n
#   * forall k, len(bf[k]) = m
type BoolFunc = List[List[bool]]

## Circuit datatypes
class LeadType(Enum):
  # Lead which is always 1/True
  TRUE = 1
  # Circuit input lead
  INPUT = 2
  # Output from a previous gate
  GATE = 3

@total_ordering
@dataclass
class Lead:
  """Specification for a leads that can be used as inputs to gates or wired to outputs."""
  gate_type : LeadType
  # INPUT or GATE number
  index : int
  # Whether or not to apply NOT to this value
  negate : bool

  def eval(self, input_vals : Sequence[bool], gate_vals : Sequence[bool]) -> bool:
    if self.gate_type == LeadType.TRUE:
      val = True
    elif self.gate_type == LeadType.INPUT:
      val = input_vals[self.index]
    elif self.gate_type == LeadType.GATE:
      val = gate_vals[self.index]
    # Negate if self.negate (using XOR)
    return val ^ self.negate
  
  def _tuple(self) -> tuple[int, int, bool]:
    return (self.gate_type.value, self.index, self.negate)
  def __lt__(self, other : Lead) -> bool:
    return self._tuple() < other._tuple()
MIN_LEAD = Lead(LeadType.TRUE, 0, False)

@total_ordering
@dataclass
class Gate:
  """AND gate with 2 inputs."""
  input1 : Lead
  input2 : Lead

  def eval(self, input_vals : Sequence[bool], gate_vals : Sequence[bool]) -> bool:
    return (self.input1.eval(input_vals, gate_vals) and 
            self.input2.eval(input_vals, gate_vals))

  # We compare input2 first so that a gate is guaranteed to be greater than
  # all its predecessor gates! Specifically:
  #   gate[n].input1 < gate[n].input2 < Lead(GATE, n, _)
  def _tuple(self) -> tuple[Lead, Lead]:
    return (self.input2, self.input1)
  def __lt__(self, other : Lead) -> bool:
    return self._tuple() < other._tuple()
MIN_GATE = Gate(MIN_LEAD, MIN_LEAD)

@dataclass
class Circuit:
  num_inputs: int
  gates: List[Gate]
  # Assign any available lead to each output.
  outputs: List[Lead]

  def eval(self, input_vals : Sequence[bool]) -> List[bool]:
    gate_vals : list[bool] = []
    for gate in self.gates:
      # Evaluate the output bit from all gates in order.
      # Gates should only depend on inputs and previously defined gates.
      gate_vals.append(gate.eval(input_vals, gate_vals))
    # Evaluate circuit outputs based on all input and gate values.
    return tuple(lead.eval(input_vals, gate_vals) for lead in self.outputs)


## Circuit enumeration
def enum_leads(num_inputs : int, num_gates : int, allow_const : bool) -> Iterator[Lead]:
  for negate in False, True:
    if allow_const:
      yield Lead(LeadType.TRUE, 0, negate)  # 1 or 0 lead
    for k in range(num_inputs):
      yield Lead(LeadType.INPUT, k, negate)
    for k in range(num_gates):
      yield Lead(LeadType.GATE, k, negate)

def enum_gate(num_inputs : int, num_prev_gates : int, prev_gate : Gate) -> Iterator[Gate]:
  # Optimizations:
  #   1) A AND B = B AND A, so only consider one of them
  #   2) Exclude A AND A
  #   3) Exclude TRUE/FALSE as inputs
  for (lead1, lead2) in itertools.combinations(
      enum_leads(num_inputs, num_prev_gates, False), 2):
    gate = Gate(lead1, lead2)
    # Require gates to be enumerated in canonical order
    if gate > prev_gate:
      yield gate

def enum_gates(num_inputs : int, num_gates : int) -> Iterator[List[Gate]]:
  if num_gates == 0:
    yield tuple()
  elif num_gates == 1:
    for gate in enum_gate(num_inputs, 0, MIN_GATE):
      yield (gate,)
  else:
    for sub in enum_gates(num_inputs, num_gates - 1):
      prev_gate = sub[-1]
      for gate in enum_gate(num_inputs, num_gates - 1, prev_gate):
        yield sub + (gate,)

def enum_outputs(num_inputs : int, num_outputs : int, num_gates : int) -> Iterator[List[Lead]]:
  yield from itertools.product(enum_leads(num_inputs, num_gates, True), repeat=num_outputs)

def enum_circuits(num_inputs : int, num_outputs : int , num_gates : int) -> Iterator[Circuit]:
  """Enumerate all circuits with precise numbers of inputs, outputs and gates."""
  for gates in enum_gates(num_inputs, num_gates):
    for outputs in enum_outputs(num_inputs, num_outputs, num_gates):
      yield Circuit(num_inputs, gates, outputs)

# Naive enumeration (gates unordered, leads unordered) but still only feed-forward:
#   NC(n,m,t) = 2^{2t+m} ((n+t)!/n!)^2 (n+t+1)^m
#             < (2(n+t+1))^{2t+m}
#             > (2n)^{2t} (2(n+t+1))^m
#
# Gate inputs ordered (force gates to have different inputs and always left < right):
#   NC(n,m,t) = 2^{m-t} (2(n+t))!/(2n)! (n+t+1)^m
#     ~ 2^t improvement
#
# Gates ordered (gates must have input > previous gate input):
#   ~ t! improvement? Not so high, all gate orderings are not possible!

## Circuit evalutation
def semantics(circuit : Circuit) -> BoolFunc:
  """Evaluate the boolean function that this circuit computes."""
  results = []
  for assignments in itertools.product((False, True), repeat=circuit.num_inputs):
    results.append(circuit.eval(assignments))
  return tuple(results)

def explore_semantics(num_inputs : int, num_outputs : int) -> None:
  """Explore minimal AIGs for computing all Boolean functions of a given size."""
  start_time = time.time()
  funcs = set()
  num_circuits = 0
  for num_gates in itertools.count(0):
    for c in enum_circuits(num_inputs, num_outputs, num_gates):
      funcs.add(semantics(c))
      num_circuits += 1
    print(f"{num_inputs:2d} {num_outputs:2d} {num_gates:2d} : {len(funcs):11_d} {num_circuits:15_d}  ({time.time() - start_time:8_.2f}s)")

  return num_circuits, len(funcs)
# NS(n,m,t) <= {2^m}^{2^n}
# NS(n,0,t) = 1
# NS(n,m,0) = (2n+2)^m
# NS(n,1,1) = 4 n^2 - 10n + 8?


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("num_inputs", type=int)
  parser.add_argument("num_outputs", type=int)
  args = parser.parse_args()

  explore_semantics(args.num_inputs, args.num_outputs)

if __name__ == "__main__":
  main()
