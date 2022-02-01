"""
Code to explore optimal play in Super Auto Pets.
"""

import numpy

import battle
import compare
import pets
import teams
import util


def boost(pet, attack, health):
  pet = pet.copy()
  pet.attack += attack
  pet.health += health
  return pet

def with_horse_buff(team):
  num_horses = sum(1 for pet in team if pet.name == "Horse")
  if num_horses == 0:
    return team
  else:
    new_team = []
    horse_count = 0
    for pet in team:
      if pet.name == "Horse":
        horse_count += 1
        # This horse is boosted by all horses behind it (assuming that puting
        # the buff one in front is best ...)
        new_team.append(boost(pet, num_horses - horse_count, 0))
      else:
        # Non-horses are assumed bought after horses, so get full buff.
        new_team.append(boost(pet, num_horses, 0))
    return new_team

def list_round1_teams():
  # TODO: We hand-build these teams using a heuristic, instead allow arbitrary
  # team_building strategy.
  all_teams = []
  # TODO: We only consider these 6 pets right now because others
  # are strictly worse than Fish (to keep on team, for round1 only).
  good_pets = [pets.Ant, pets.Cricket, pets.Fish, pets.Horse, pets.Mosquito,
               pets.Otter]
  # First consider all 3 pet teams (giving bonuses for teams with Horses)
  for schema in util.cartesian_product(good_pets, 3):
    team = [pet_class() for pet_class in schema]
    team = with_horse_buff(team)
    # TODO: Otter bonus ...
    all_teams.append(team)
  # Second consider all 2 pet teams boosted by:
  #  1) buying and selling a Duck first,
  #  2) selling a Beaver last
  for schema in util.cartesian_product(good_pets, 2):
    # Duck boosted
    all_teams.append([boost(pet_class(), 1, 1) for pet_class in schema])
    # Beaver boosted
    all_teams.append([boost(pet_class(), 0, 1) for pet_class in schema])
  return [teams.Team(pets_list) for pets_list in all_teams]


def try_all_round1():
  util.log("Enumerating all possible teams")
  all_teams = list_round1_teams()
  util.log(f"Found {len(all_teams):_d} teams")

  util.log(f"Simulating all {len(all_teams)**2:_d} pairings")
  outcomes = compare.round_robin(all_teams)

  util.log("Summarizing results")
  print("Teams which lost least:")
  (uniform_order_indexes, sum_outcomes) = compare.uniform_order(outcomes)
  for place, index in enumerate(uniform_order_indexes[:20]):
    print(f" {place+1:3d}  {str(all_teams[index]):40s} {sum_outcomes[index]}")

  print()
  print("Top teams were defeated by:")
  for place, index in enumerate(uniform_order_indexes[:3]):
    print(f" {place+1:3d}  {str(all_teams[index]):s}  defeated by:")
    for oppentent_index, outcome in enumerate(outcomes[index]):
      if outcome.lose > 0:
        print(f"      - {str(all_teams[oppentent_index]):s}")

  util.log("Searching for optimal strategy")
  strategy = compare.gradient_decent(outcomes)
  strong_teams = []
  for index in range(len(all_teams)):
    if strategy[index] > 0.1:
      print(f" {strategy[index]:4.0%}  {index:4d}  {str(all_teams[index])}")
      strong_teams.append(all_teams[index])

  util.log("Retry search")
  outcomes = compare.round_robin(strong_teams)
  print(numpy.matrix([[res.win - res.lose for res in row]
                      for row in outcomes]))
  strategy = compare.gradient_decent(outcomes)
  for index in range(len(strong_teams)):
    print(f" {strategy[index]:4.0%}  {index:4d}  {str(strong_teams[index])}")
  print(compare.nash_equilibrium(outcomes))

  util.log("Done")

try_all_round1()
