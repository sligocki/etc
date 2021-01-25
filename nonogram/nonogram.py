# Exploration of Nonogram solvers, combinatorics, etc.

class NoSolution(Exception):
  """No possible solution to this Nonogram."""
  pass

BLANK = "."
FULL = "X"

class Nonogram:
  def __init__(self, row_specs, col_specs):
    self.row_specs = row_specs
    self.col_specs = col_specs
    # First index row, second index col.
    # Initialized to all None since we don't know color yet.
    self.grid = [[None for _ in range(len(self.col_specs))]
                 for _ in range(len(self.row_specs))]

  def GetDim(self, direction):
    if direction == 0:
      return len(self.row_specs)
    else:
      return len(self.col_specs)

  def GetLine(self, direction, index):
    if direction == 0:
      # Row
      return (self.row_specs[index], self.grid[index])
    else:
      assert direction == 1
      # Column
      return (self.col_specs[index], [row[index] for row in self.grid])

  def SetLine(self, direction, index, line):
    if direction == 0:
      # Row
      self.grid[index] = line
    else:
      assert direction == 1
      # Column
      for i, row in enumerate(self.grid):
        row[index] = line[i]

  def GridStr(self):
    return "\n".join("".join(row) for row in self.grid)


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
    if old_line[i] != None and new_line[i] != old_line[i]:
      return False
  return True

def UpdateLine(spec, old_line):
  pos_lines = [line for line in EnumLines(spec, len(old_line))
               if MatchesLine(line, old_line)]
  if len(pos_lines) == 0:
    raise NoSolution

  new_line = [None for _ in range(len(old_line))]
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
def EnumGrid(num_rows, num_cols):
  pass

def EnumRows(grid):
  for row in grid:
    yield row

def EnumCols(grid):
  for index in range(len(grid[0])):
    yield [row[index] for row in grid]

def Grid2Spec(grid):
  row_specs = tuple(Line2Spec(line) for line in EnumRows(grid))


# Test LineSolve
clown = Nonogram(row_specs = [[4], [1, 3], [10], [1, 1, 1, 1], [1, 2, 1],
                              [1, 2, 1], [1, 1, 1], [1, 2, 1], [1, 1], [8]],
                 col_specs = [[1, 2], [2, 2, 1], [2, 2], [1, 2, 1], [1, 1, 2, 1, 1],
                              [3, 2, 1, 1], [4, 1, 1], [2, 2], [2, 2, 1], [1, 2]])
print(LineSolve(clown).GridStr())
