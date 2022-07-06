import math

import game_tree
import position

# For imperfect information version of game, we search for a (mixed) Nash Equilibrium.
# Specifically, we search for a pair of strategies where knowing your opponent's
# complete strategy (but not knowing their secret goal), you are not incentivized
# to change your strategy.

# To check if we have found a Nash Equilibrium, every game path must be evaluated
# seperately. At each node in the game tree, the current player can figure out
# the probability that their opponent has each goal based upon knowing their
# exact (mixed) strategy and the sequence of moves they have made.

def enum_games(tree, strategy, trace):
  pos = trace[-1]

  if not tree.children[pos]:
    # Game Over. 100% of continuations end here.
    return {(pos,) : 1.0}
  else:
    player = position.get_player(pos)
    probs = {}
    for next_pos, prob in strategy(trace):
      next_probs = enum_games(tree, strategy, trace + [next_pos])




def check_nash_equilibrium(tree, strategy):
  pass


def test():
  pass

if __name__ == "__main__":
  test()
