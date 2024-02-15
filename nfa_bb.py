"""
Based on question from Discord:
  What's the smallest N that there's N-state NFA that accepts all strings up to length N (inclusive), but isn't universal?

I'm investigating specifically the unary case here.
"""

from collections.abc import Iterable, Iterator
import string
import time


State = int
StateSet = frozenset[State]

def state_str(state : State):
  return string.ascii_uppercase[state]
def states_str(states : StateSet):
  return "".join(state_str(s) for s in sorted(states))

class NFA:
  def __init__(self, start_state : StateSet, trans : list[StateSet]):
    self.start_state = start_state
    self.trans = trans

  def step(self, state : StateSet):
    if state:
      return frozenset.union(*[self.trans[x] for x in state])
    else:
      # Empty -> Empty
      return frozenset()

  def __repr__(self):
    trans_str = " ".join(f"{state_str(state_in)}->{states_str(states_out)}"
                         for (state_in, states_out) in enumerate(self.trans))
    return f"NFA[Start->{states_str(self.start_state)}  {trans_str}]"


def sim_nfa(nfa : NFA) -> list[StateSet]:
  """Simulate nfa on unary tape until states reach a cycle (at which point they will repeat forever). Return path of states (each is really a list of reachable base states) reached at each step until the cycle starts."""
  state = nfa.start_state
  visited = set()
  path = []
  while state not in visited:
    path.append(state)
    visited.add(state)
    state = nfa.step(state)
  return path


def is_superset(x : StateSet, ys : Iterable[StateSet]) -> bool:
  for y in ys:
    if x.issuperset(y):
      return True
  return False

def score_path(path : list[StateSet]) -> int:
  """Find latest step we can first reject. This is the largest index (n) such that path[n] is not a superset of any path[k] for k < n."""
  visited : set[StateSet] = set()
  for n, state in enumerate(path):
    if not is_superset(state, visited):
      best = n
    visited.add(state)
  return best


def enum_subsets(a : int, b : int) -> Iterator[StateSet]:
  """Enumerate all subsets of range(size)."""
  if a == b:
    yield frozenset()
  else:
    for sub in enum_subsets(a+1, b):
      yield sub
      yield frozenset([a]) | sub

def enum_subset_lists(size : int, count : int) -> Iterator[list[StateSet]]:
  """Enumerate all sequences of count subsets of range(size)."""
  if count == 0:
    yield []
  else:
    for sub in enum_subset_lists(size, count - 1):
      for new in enum_subsets(0, size):
        yield sub + [new]

def enum_nfas(num_states : int) -> Iterator[NFA]:
  # All NFAs can be normalized so all start states are at beginning.
  # So we can restrict our consideration to NFAs with start states [0, n] for all n
  for start_size in range(1, num_states + 1):
    start = frozenset(range(start_size))
    for trans in enum_subset_lists(num_states, num_states):
      yield NFA(start, trans)


def search(num_states : int):
  max_score = -1
  best_nfa = None
  for nfa in enum_nfas(num_states):
    path = sim_nfa(nfa)
    score = score_path(path)
    if score > max_score:
      if score > num_states:
        print(f"   {score:3d} {repr(nfa):40s} ({time.process_time():6.1f}s)")
      max_score = score
      best_nfa = nfa
  return (max_score, best_nfa)


def main():
  champ = NFA(frozenset([0,3]), [
    frozenset([1]),
    frozenset([2]),
    frozenset([0]),

    frozenset([4]),
    frozenset([5]),
    frozenset([6]),
    frozenset([3]),
  ])
  score = score_path(sim_nfa(champ))
  print(f"Champ 7: {score} {repr(champ)}")

  for num_states in range(1, 7):
    max_score, best_nfa = search(num_states)
    print(f"{num_states:2d} {max_score:3d} {repr(best_nfa):40s} ({time.process_time():6.1f}s)")

main()
