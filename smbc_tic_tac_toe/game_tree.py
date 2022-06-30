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

  def num_games(self, pos = None):
    if not pos:
      pos = self.init_pos
    if not self.children[pos]:
      # If there are no following moves, this is a single completed game trace.
      return 1
    else:
      # Otherwise, add up all the following counts.
      # Note: This is inefficient because it's not memoized ... but I think it
      # doesn't matter for tic-tac-toe b/c it's small enough ...
      return sum(self.num_games(next_pos) for next_pos in self.children[pos])


def test():
  tree = Tree()
  tree.build()
  print("Number of pos_to_next:", tree.num_positions())
  print("Number of games:", tree.num_games())


if __name__ == "__main__":
  test()
