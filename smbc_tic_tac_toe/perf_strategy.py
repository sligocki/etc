import math

import game_tree
import position


def perfect_info_min_max(tree, eval_leaf):
  """Evaluate game where players know each other's strategy (perfect information)."""
  # Values that X and O place on each position.
  value = { player: {} for player in position.players }
  for pos, children in tree.walk_back():
    cur_player = position.get_player(pos)
    if not children:
      # Game Over. Evaluate using player's goal.
      for player in position.players:
        value[player][pos] = eval_leaf[player](tree.winner[pos])
    else:
      other_player = position.other_player(cur_player)
      # Game continues. Current player maximizes value
      # (We use -opponent's score just to make sure that we can break ties consistently ...)
      best_move = max(children,
                      key = lambda pos: (value[cur_player][pos], -value[other_player][pos]))
      for player in position.players:
        value[player][pos] = value[player][best_move]
  return {player: value[player][tree.init_pos] for player in position.players}

def strat_equal(desired_outcome):
  def strat(winner):
    if winner == desired_outcome:
      return 1
    else:
      return 0
  return strat

kStrat = {
  player : {
    "W" : strat_equal(player),
    "D" : strat_equal(None),
    "L" : strat_equal(position.other_player(player)),
  }
  for player in position.players
}

def zero_sum(base_strat):
  def player_strat(player):
    def strat(winner):
      return base_strat[player](winner) - base_strat[position.other_player(player)](winner)
    return strat

  return {player: player_strat(player) for player in base_strat}


def test():
  tree = game_tree.Tree()
  tree.build()

  for goal_X in "W", "D", "L":
    for goal_Y in "W", "D", "L":
      print(goal_X, "vs.", goal_Y)
      base_strat = {"X": kStrat["X"][goal_X], "O": kStrat["O"][goal_Y]}
      zs_strat = zero_sum(base_strat)

      print(" * Base:", perfect_info_min_max(tree, base_strat))
      print(" * Zero Sum:", perfect_info_min_max(tree, zs_strat))


if __name__ == "__main__":
  test()
