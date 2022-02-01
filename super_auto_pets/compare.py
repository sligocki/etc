import numpy

import battle
import util


def round_robin(teams):
  """Perform round-robin tournament amont collection of teams and return outcomes."""
  # outcomes[i][j] is the result of teams[i] vs. teams[j]
  outcomes = []
  for team_a in teams:
    outcomes_a = []
    for team_b in teams:
      outcomes_a.append(battle.battle(team_a, team_b))
    outcomes.append(outcomes_a)
  return outcomes

def min_losses_max_wins_key(result):
  """A comp_key that sorts for minimizing losses (maximizing wins as a tiebreaker)."""
  return (result.lose, -result.win)

def uniform_order(outcomes, comp_key=min_losses_max_wins_key):
  """Order round-robin outcomes by simple strategy by comparing to all possible opponents with equal weight. This is the optimal strategy if your opponent is chosen uniformly at random from the distribution."""
  sum_outcomes = []
  for outcomes_a in outcomes:
    sum_outcomes.append(battle.BattleResult(
      win  = sum(res.win  for res in outcomes_a),
      tie  = sum(res.tie  for res in outcomes_a),
      lose = sum(res.lose for res in outcomes_a)))
  return (util.argsort(sum_outcomes, key=comp_key), sum_outcomes)


def gradient_decent(outcomes, num_iterations=100):
  """Attempt to approximate a Nash Equilibrium mixed strategy by gradient decent starting at uniform choise over all teams and moving in the direction of the "optimal response"."""
  num_teams = len(outcomes)
  # Payoff is -1 for a loss, 0 for win or tie.
  payoff_matrix = numpy.matrix([[res.win-res.lose for res in row]
                                for row in outcomes])
  # Build strategy from preferences
  strategy = numpy.matrix([[1.] for _ in range(num_teams)])
  # Normalize
  strategy = numpy.divide(strategy, strategy.sum())

  for _ in range(num_iterations):
    #print("#", _)
    # If opponent uses strategy, what are the payoffs for me for each
    # pure strategy?
    payoffs = numpy.matmul(payoff_matrix, strategy)
    max_payoff = max(payoffs)
    opt_response = numpy.zeros((num_teams, 1))
    # Average old strategy with the optimal response.
    for i in range(num_teams):
      if payoffs[i, 0] > max_payoff - 0.0001:
        #print(" .", i)
        opt_response[i, 0] = 1
    # Normalize and make smaller so that it only nudges the solution.
    opt_response = numpy.divide(opt_response, opt_response.sum() * 10)

    strategy = numpy.add(strategy, opt_response)
    strategy = numpy.divide(strategy, strategy.sum())

  return list(strategy.flat)

def nash_equilibrium(outcomes):
  # TODO: This only works if there actually is a complete mixed strategy
  # (using >0 prob for all teams). In reality, we need to check for strategies
  # which use a subset of teams.
  num_teams = len(outcomes)
  # Payoff is -1 for a loss, 0 for win or tie.
  payoff_matrix = numpy.matrix([[1 - 2 * res.lose for res in row]
                                for row in outcomes])
  print(payoff_matrix)
  inv_pay_mat = numpy.linalg.inv(payoff_matrix)
  print(inv_pay_mat)
  nash_strat = numpy.matmul(inv_pay_mat, numpy.ones((num_teams, 1)))
  print(nash_strat)
  nash_strat = numpy.divide(nash_strat, nash_strat.sum())
  return list(nash_strat.flat)


if __name__ == "__main__":
  import teams

  ex_teams = teams.example_teams()
  outcomes = round_robin(ex_teams)
  print(numpy.matrix([[res.win - res.lose for res in row]
                      for row in outcomes]))

  strategy = gradient_decent(outcomes)
  print(strategy)
  for index in range(len(ex_teams)):
    print(f" {strategy[index]:4.0%}  {str(ex_teams[index])}")

  print(nash_equilibrium(outcomes))
