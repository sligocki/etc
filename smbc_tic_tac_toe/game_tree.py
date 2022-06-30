import position


class Tree:
  def __init__(self):
    self.init_pos = position.init_pos
    # Map from all positions to list of children.
    # Note: If there are no children, that means the game is over.
    self.children = {}
    # Map from position to winner.
    # Value is either a player who won or None.
    # None indicates that either game is not finished or it is a Draw.
    self.winner = {}

  def build(self):
    todo_pos = [self.init_pos]
    while todo_pos:
      pos = todo_pos.pop()
      self.winner[pos] = position.eval_pos(pos)
      if self.winner[pos]:
        # Game is over, no following moves.
        self.children[pos] = []
      else:
        # Game is still going, consider following moves.
        if pos not in self.children:
          self.children[pos] = position.list_moves(pos)
          todo_pos.extend(self.children[pos])

  def num_positions(self):
    return len(self.children)

  def _walk_help(self, visited, pos):
    if pos not in visited:
      visited.add(pos)
      # 1) Yield all descendants
      for next_pos in self.children[pos]:
        for p in self._walk_help(visited, next_pos):
          yield p
      # 2) Yield self
      yield pos

  def walk_back(self):
    """Enumerate all postitions in the game tree backwards, starting from leaf
    nodes. You are guaranteed that you will only see a position after all of
    it's children."""
    visited = set()
    for pos in self._walk_help(visited, self.init_pos):
      yield pos, self.children[pos]


def num_games(tree):
  num_subgames = {}
  for pos, children in tree.walk_back():
    if not children:
      # If there are no following moves, this is a single completed game trace.
      num_subgames[pos] = 1
    else:
      # Otherwise, add up all the following counts.
      # Note: This is inefficient because it's not memoized ... but I think it
      # doesn't matter for tic-tac-toe b/c it's small enough ...
      num_subgames[pos] = sum(num_subgames[next_pos] for next_pos in children)
  return num_subgames[tree.init_pos]


def test():
  tree = Tree()
  tree.build()
  print("Number of pos_to_next:", tree.num_positions())
  print("Number of games:", num_games(tree))


if __name__ == "__main__":
  test()
