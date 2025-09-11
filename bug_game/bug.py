from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
import math
import string
from typing import Iterator


# Encoding: Wall = inf, otherwise value equals number of times visited.
# Thus we can use same algorithm to find next cell to travel to by minimizing over neighbor values.
# Nees to allow float b/c math.inf is technially a float ...
type Cell = int | float
WALL : Cell = math.inf

@dataclass(frozen=True)
class Loc:
  x: int
  y: int

  def __add__(self, other: Loc) -> Loc:
    return Loc(self.x + other.x, self.y + other.y)
  
  def __repr__(self) -> str:
    return f"({self.x}, {self.y})"
assert Loc(1, 2) == Loc(1, 2)
assert Loc(1, 2) + Loc(-1, 1) == Loc(0, 3)

# Direction is just a location offset
type Dir = Loc

# Possible walk directions in priority order
DIRS : list[Dir] = [
  Loc( 0,  1),  # Down
  Loc( 1,  0),  # Right
  Loc( 0, -1),  # Up
  Loc(-1,  0),  # Left
]
START_DIR : Dir = Loc( 0, -1)  # Up

@dataclass
class Board:
  # Stored as data[y][x]
  data: list[list[Cell]]

  def x_size(self) -> int:
    return len(self.data[0])
  def y_size(self) -> int:
    return len(self.data)

  def __getitem__(self, loc: Loc) -> Cell:
    return self.data[loc.y][loc.x]
  def __setitem__(self, loc: Loc, val: Cell) -> None:
    self.data[loc.y][loc.x] = val

  def copy(self) -> Board:
    return Board(copy.deepcopy(self.data))
  
  def __iter__(self) -> Iterator[Loc]:
    for x in range(1, self.x_size() - 1):
      for y in range(1, self.y_size() - 1):
        yield Loc(x, y)

  def max(self) -> int:
    return max(cost for loc in self if (cost := self[loc]) != WALL)

@dataclass
class State:
  """Full game state: board description, bug position and visit count."""
  board: Board
  bug_loc: Loc
  bug_dir: Dir
  dest_loc: Loc

  def is_running(self) -> bool:
    return self.bug_loc != self.dest_loc

  def step(self) -> None:
    self.board[self.bug_loc] += 1
    best_dir = None
    min_cost = math.inf
    # Move priority: Current direction, then all others (in specific DIRS order).
    # Note: This technically searches one direction twice ...
    for dir in [self.bug_dir, *DIRS]:
      loc = self.bug_loc + dir
      cost = self.board[loc]
      if cost < min_cost:
        min_cost = cost
        best_dir = dir
    assert best_dir
    # Move one step `best_dir`
    self.bug_dir = best_dir
    self.bug_loc += best_dir

  def copy(self) -> State:
    return State(self.board.copy(), self.bug_loc, self.bug_dir, self.dest_loc)


def runtime(pos: State) -> int:
  num_steps = 0
  while pos.is_running():
    pos.step()
    num_steps += 1
    # print(num_steps, pos.bug_loc)
    # print(board_str(pos))
    # print
  return num_steps

def is_solvable(pos: State) -> bool:
  """DFS search of space to find if a path exists from bug to destination."""
  visited = {pos.bug_loc}
  todo = [pos.bug_loc]
  while todo:
    loc = todo.pop()
    for dir in DIRS:
      new_loc = loc + dir
      if new_loc == pos.dest_loc:
        # DFS found a path
        return True
      if new_loc not in visited:
        visited.add(new_loc)
        if pos.board[new_loc] != WALL:
          todo.append(new_loc)
  # DFS failed to connect to dest
  return False

def board_to_state(board: Board) -> State:
  return State(
    board = board,
    bug_loc = Loc(1, 1),
    bug_dir = START_DIR,
    dest_loc = Loc(board.x_size() - 2, board.y_size() - 2))


def parse_board(board_str: str) -> State:
  # NOTE: This depends upon the board string having walls on full parimeter!
  board : list[list[Cell]]= []
  for line in board_str.splitlines():
    if line.strip():
      # @ is wall, everything else is open.
      board.append([WALL if x in "@#" else 0 for x in line.strip()])
  return board_to_state(Board(board))


HEATMAP_CHARS_BASIC = string.digits + string.ascii_lowercase
HEATMAP_CHARS_LOG = string.ascii_lowercase
def heatmap_encode(val, max_val):
  if max_val < len(HEATMAP_CHARS_BASIC):
    return HEATMAP_CHARS_BASIC[val]
  else:
    x = len(HEATMAP_CHARS_LOG) * math.log(val) / math.log(max_val + 1)
    return HEATMAP_CHARS_LOG[int(x)]

def board_to_str(state: State) -> str:
  max_cost = state.board.max()
  max_log_cost = math.log2(max_cost + 1) if max_cost else 1
  lines = []
  for y in range(state.board.y_size()):
    line = []
    for x, cell in enumerate(state.board.data[y]):
      if Loc(x,y) == state.bug_loc:
        line.append("B")
      elif Loc(x,y) == state.dest_loc:
        line.append("F")
      elif cell == WALL:
        line.append("#")
      elif cell == 0:
        line.append(".")
      else:
        line.append(heatmap_encode(cell, max_cost))
    lines.append("".join(line))
  return "\n".join(lines)

def show(board_str: str) -> None:
  state = parse_board(board_str)
  print(board_to_str(state))
  if is_solvable(state):
    score = runtime(state)
    print("Score:", score)
    print("Max Visit Count:", state.board.max())
    print(board_to_str(state))
    print()
  else:
    print("No path to destination")


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("infile")
  args = parser.parse_args()

  with open(args.infile) as f:
    show(f.read())

if __name__ == "__main__":
  main()
