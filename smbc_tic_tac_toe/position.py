"""
Basic position encoding.

Exports simple interface:
 * init_pos : Position
 * players : list(Players)
 * get_player(pos : Position) -> Player
 * other_player(player : Player) -> Player
 * eval_pos(pos : Position) -> Player or None
 * list_moves(pos : Position) -> list(Position)
"""

players = ["X", "O"]
_kBlank = "."
init_pos = (_kBlank * 9, "X")

def get_player(pos):
  board, player = pos
  return player

def other_player(player):
  _kOtherPlayer = {"X" : "O", "O": "X"}
  return _kOtherPlayer[player]

_kWinPatterns = (
  [[c + 3*r for c in range(3)] for r in range(3)] +  # Rows
  [[c + 3*r for r in range(3)] for c in range(3)] +  # Cols
  [[0, 4, 8], [2, 4, 6]]  # Diagonals
)
def eval_pos(pos):
  """Evalutate the position to see if it's a game over and who won.
  Returns winning player (or None if nobody has won). Note: Assumes valid
  position, i.e. no pos with two different winners!"""
  board, player = pos
  for locs in _kWinPatterns:
    vals = set(board[loc] for loc in locs)
    if len(vals) == 1:
      val = vals.pop()
      if val != _kBlank:
        return val
  return None

def _move(old_board : str, index : int, player : str) -> str:
  assert old_board[index] == _kBlank
  new_board = list(old_board)
  new_board[index] = player
  return "".join(new_board)

def list_moves(pos):
  """List following positions. Note: Only call this for positions that are not
  already won. It does not check for pos being already won."""
  board, player = pos
  new_poses = []
  for i, cell in enumerate(board):
    if cell == _kBlank:
      new_board = _move(board, i, player)
      new_poses.append((new_board, other_player(player)))
  return new_poses
