class State:
  def __init__(self, friends, enemies):
    self.friends = friends
    self.enemies = enemies
    self.trigger_queue = []

  def __str__(self):
    return " ".join(str(pet) for pet in self.friends)

  def start_battle(self):
    for i, pet in enumerate(self.friends):
      if "start_battle" in pet.triggers:
        self.trigger_queue.append((pet.triggers["start_battle"], i))

  def apply_attack(self):
    damage = self.enemies[0].attack
    # TODO: Shield
    #print(" - Pre-damage:", damage, self.friends[0])
    self.friends[0].health -= damage
    #print(" - Post-damage:", self.friends[0])
    # TODO: Trigger hurt (if not dead).

  def apply_feints(self):
    """See if anyone feinted and remove them."""
    feint_indexes = []
    for i, pet in enumerate(self.friends):
      if pet.health <= 0:
        feint_indexes.append(i)
        if "feint" in pet.triggers:
          self.trigger_queue.append((pet.triggers["feint"], i))
    # We have to delete in reverse order so that indexes remain valid.
    for i in reversed(feint_indexes):
      del self.friends[i]

  def apply_triggers(self):
    for (action, trigger_loc) in self.trigger_queue:
      type = action[0]
      if type == "summon":
        _, pet_class = action
        pet = pet_class()
        self.apply_trigger_summon(pet, trigger_loc)
      elif type == "boost":
        _, where, count, boost_attack, boost_health = action
        self.apply_trigger_boost(where, count, boost_attack, boost_health,
                                 trigger_loc)
      elif type == "damage":
        _, where, count, damage_amount = action
        self.apply_trigger_damage(where, count, damage_amount, trigger_loc)
      else:
        raise Exception(action)
    self.trigger_queue = []

  def apply_trigger_summon(self, pet, trigger_loc):
    # TODO: These locs might be invalidated if there's multiple summon triggers in the queue at the same time ...
    # TODO: Check that we are not adding too many friends (max 5).
    self.friends.insert(trigger_loc, pet)
    for other_pet in self.friends:
      if "friend_summon" in other_pet.triggers:
        self.trigger_queue.append((other_pet.triggers["friend_summon"],
                                   trigger_loc))

  def apply_trigger_boost(self, where, count, boost_attack, boost_health,
                          trigger_loc):
    if where == "trigger":
      assert count == None
      targets = [trigger_loc]
    elif where == "random_friend":
      # If there aren't enough friends, some reps will fizzle.
      count = min(count, len(self.friends))
      # TODO: Explore all possible target combinations.
      # For right now we just always target the first pets in line.
      targets = list(range(count))
    else:
      raise Exception(where)

    for target in targets:
      self.friends[target].attack += boost_attack
      self.friends[target].health += boost_health

  def apply_trigger_damage(self, where, count, damage_amount, trigger_loc):
    if where == "random_enemy":
      # If there aren't enough friends, some reps will fizzle.
      count = min(count, len(self.enemies))
      # TODO: Explore all possible target combinations.
      # For right now we just always target the first pets in line.
      targets = list(range(count))
    else:
      raise Exception(where)

    for target in targets:
      # TODO: Shield, trigger hurt, etc.
      self.enemies[target].health -= damage_amount


class BattleResult:
  def __init__(self, win, tie, lose):
    self.win = win
    self.tie = tie
    self.lose = lose

  def __str__(self):
    return f"{self.win:.2f} Win, {self.tie:.2f} Tie, {self.lose:.2f} Lose"

Win  = BattleResult(1, 0, 0)
Tie  = BattleResult(0, 1, 0)
Lose = BattleResult(0, 0, 1)


def resolve_triggers(states):
  # Repeatedly apply triggers and check for any animals who feinted until
  # there are not triggers left.
  while states[0].trigger_queue or states[1].trigger_queue:
    for state in states:
      state.apply_triggers()
    for state in states:
      state.apply_feints()

def battle(team_a, team_b, verbose=False):
  # Make copies so that we don't modify the passed in teams.
  team_a = team_a.copy()
  team_b = team_b.copy()
  states = [
    State(team_a, team_b),
    State(team_b, team_a),
  ]

  for state in states:
    state.start_battle()
  resolve_triggers(states)
  while team_a and team_b:
    if verbose:
      print()
      print(" * Team A:", states[0])
      print(" * Team B:", states[1])
    for state in states:
      state.apply_attack()
    for state in states:
      state.apply_feints()
    resolve_triggers(states)

  if verbose:
    print()
    print("Battle Done")
    print(" * Team A:", states[0])
    print(" * Team B:", states[1])

  # Evaluate winner
  if team_a and not team_b:
    return Win
  if team_b and not team_a:
    return Lose
  if not team_a and not team_b:
    return Tie
