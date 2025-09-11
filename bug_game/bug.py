from __future__ import annotations

from dataclasses import dataclass
import math


# Encoding: Wall = inf, otherwise value equals number of times visited.
# Thus we can use same algorithm to find next cell to travel to by minimizing over neighbor values.
# Nees to allow float b/c math.inf is technially a float ...
type Cell = int | float

@dataclass
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

@dataclass
class Board:
  # Stored as data[y][x]
  data: list[list[Cell]]

  def y_size(self) -> int:
    return len(self.data)

  def __getitem__(self, loc: Loc) -> Cell:
    return self.data[loc.y][loc.x]
  def __setitem__(self, loc: Loc, val: Cell) -> None:
    self.data[loc.y][loc.x] = val

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

def runtime(pos: State) -> int:
  num_steps = 0
  while pos.is_running():
    pos.step()
    num_steps += 1
    # print(num_steps, pos.bug_loc)
    # print(board_str(pos))
    # print
  return num_steps

def parse_board(board_str: str) -> State:
  board : list[list[Cell]]= []
  for line in board_str.splitlines():
    if line.strip():
      # @ is wall, everything else is open.
      # Add extra walls on left and right
      board.append([math.inf] + [math.inf if x == "@" else 0 for x in line.strip()] + [math.inf])
  # Add extra walls on top and bottom
  width = len(board[0])
  board = [[math.inf]*width] + board + [[math.inf]*width]
  height = len(board)
  # Start at top-left
  start = Loc(1, 1)
  # Start dir is UP
  dir = Loc(0, 1)
  # End at bottom-right
  dest = Loc(width - 2, height - 2)
  return State(Board(board), start, dir, dest)

def board_to_str(state: State) -> str:
  lines = []
  for y in range(state.board.y_size()):
    line = []
    for x, cell in enumerate(state.board.data[y]):
      if Loc(x,y) == state.bug_loc:
        line.append("B")
      elif Loc(x,y) == state.dest_loc:
        line.append("F")
      elif cell == math.inf:
        line.append("@")
      elif cell < 10:
        line.append(str(cell))
      else:
        line.append("+")
    lines.append("".join(line))
  return "\n".join(lines)

def show(board_str: str) -> None:
  state = parse_board(board_str)
  print(board_to_str(state))
  score = runtime(state)
  print("Score:", score)
  print(board_to_str(state))

show("""
....
....
.@.@
.@..""")