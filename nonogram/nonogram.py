# Exploration of Nonogram solvers, combinatorics, etc.

import collections


class NoSolution(Exception):
  """No possible solution to this Nonogram."""
  pass

UNKNOWN = "?"
BLANK = "."
FULL = "X"

class Grid:
  def __init__(self, *, num_rows=None, num_cols=None, grid=None):
    if grid:
      self.grid = grid
    else:
      # First index row, second index col.
      # Initialized to all UNKNOWN since we don't know color yet.
      self.grid = [[UNKNOWN for _ in range(num_cols)] for _ in range(num_rows)]

  def GetLine(self, direction, index):
    if direction == 0:
      # Row
      return self.grid[index]
    else:
      assert direction == 1
      # Column
      return [row[index] for row in self.grid]

  def SetLine(self, direction, index, line):
    if direction == 0:
      # Row
      self.grid[index] = line
    else:
      assert direction == 1
      # Column
      for i, row in enumerate(self.grid):
        row[index] = line[i]

  def CountUnknown(self):
    return sum(row.count(UNKNOWN) for row in self.grid)

  def EnumRows(self):
    for row in self.grid:
      yield row

  def EnumCols(self):
    for index in range(len(self.grid[0])):
      yield [row[index] for row in self.grid]

  def __str__(self):
    return "\n".join("".join(row) for row in self.grid)

def ParseGrid(s):
  grid = []
  for line in s.split("\n"):
    grid.append(tuple(line))
  return Grid(grid=tuple(grid))


class Nonogram:
  def __init__(self, row_specs, col_specs):
    self.specs = [row_specs, col_specs]
    self.grid = Grid(num_rows = len(row_specs),
                     num_cols = len(col_specs))

  def GetDim(self, direction):
    return len(self.specs[direction])

  def GetLine(self, direction, index):
    return (self.specs[direction][index], self.grid.GetLine(direction, index))

  def SetLine(self, direction, index, line):
    self.grid.SetLine(direction, index, line)


# Solvers
def EnumLines(spec, line_len):
  if line_len < 0:
    # Illegal, no options.
    return

  if len(spec) == 0:
    yield [BLANK] * line_len
    return

  for first_index in range(line_len - spec[0]):
    prefix = [BLANK] * first_index + [FULL] * spec[0] + [BLANK]
    for sub in EnumLines(spec[1:], line_len - len(prefix)):
      yield prefix + sub

  # Last run in spec can end exactly at end of line without extra 0 at end.
  if len(spec) == 1 and spec[0] <= line_len:
    first_index = line_len - spec[0]
    yield [BLANK] * first_index + [FULL] * spec[0]

def MatchesLine(new_line, old_line):
  assert len(new_line) == len(old_line)
  for i in range(len(old_line)):
    if old_line[i] != UNKNOWN and new_line[i] != old_line[i]:
      return False
  return True

def UpdateLine(spec, old_line):
  pos_lines = [line for line in EnumLines(spec, len(old_line))
               if MatchesLine(line, old_line)]
  if len(pos_lines) == 0:
    raise NoSolution

  new_line = [UNKNOWN for _ in range(len(old_line))]
  for index in range(len(old_line)):
    pos_cell = set(line[index] for line in pos_lines)
    if len(pos_cell) == 1:
      new_line[index] = pos_cell.pop()
  return new_line

def LineSolve(nono):
  """Refine a Nonogram by iteratively line solving each line."""
  was_modified = True
  while was_modified:
    was_modified = False
    for direction in range(2):
      for index in range(nono.GetDim(direction)):
        spec, line = nono.GetLine(direction, index)
        new_line = UpdateLine(spec, line)
        if new_line != line:
          was_modified = True
          nono.SetLine(direction, index, new_line)
  return nono


# Enumerate puzzles
def EnumAllRows(length):
  if length == 0:
    yield []
  else:
    for sub in EnumAllRows(length - 1):
      for cell in [BLANK, FULL]:
        yield sub + [cell]

def EnumAllGrids(num_rows, num_cols):
  if num_rows == 0:
    yield []
  else:
    for sub in EnumAllGrids(num_rows - 1, num_cols):
      for row in EnumAllRows(num_cols):
        yield sub + [row]

def Line2Spec(line):
  spec = []
  chunk = 0
  for cell in line:
    if cell == BLANK:
      if chunk:
        spec.append(chunk)
        chunk = 0
    else:
      assert cell == FULL
      chunk += 1
  if chunk:
    spec.append(chunk)
  return tuple(spec)

def Grid2Spec(grid):
  row_specs = tuple(Line2Spec(line) for line in grid.EnumRows())
  col_specs = tuple(Line2Spec(line) for line in grid.EnumCols())
  return (row_specs, col_specs)


def ListNonograms(num_rows, num_cols):
  """Count number of valid Nonograms with specific dimentions."""
  specs_count = collections.Counter()
  for grid in EnumAllGrids(num_rows, num_cols):
    grid = Grid(grid=grid)
    spec = Grid2Spec(grid)
    specs_count[spec] += 1
  return [spec for spec, count in specs_count.items() if count == 1]


# Number of square Nonograms (which can be solved uniquely).
# See also: http://oeis.org/A242876
for dim in range(1, 5):
  print(dim, len(ListNonograms(dim, dim)), 2**(dim * dim))
print()

for row_spec, col_spec in ListNonograms(2, 4):
  nono = Nonogram(row_specs=row_spec, col_specs=col_spec)
  nono = LineSolve(nono)
  if nono.grid.CountUnknown() > 0:
    print(row_spec, col_spec)
    print(str(nono.grid))
    print()
print()

# Grid2Spec example
snake = ParseGrid(
  "XXXXX\n"
  "X....\n"
  "XXXXX\n"
  "....X\n"
  "XXXXX"
)
print("Grid2Spec:", Grid2Spec(snake))
print()

# LineSolve example
clown = Nonogram(row_specs = [[4], [1, 3], [10], [1, 1, 1, 1], [1, 2, 1],
                              [1, 2, 1], [1, 1, 1], [1, 2, 1], [1, 1], [8]],
                 col_specs = [[1, 2], [2, 2, 1], [2, 2], [1, 2, 1], [1, 1, 2, 1, 1],
                              [3, 2, 1, 1], [4, 1, 1], [2, 2], [2, 2, 1], [1, 2]])
print(str(LineSolve(clown).grid))
