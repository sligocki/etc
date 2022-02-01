class Pet:
  def __init__(self, name, attack, health):
    self.name = name
    self.attack = attack
    self.health = health
    self.level = 1
    self.merged_count = 1
    self.triggers = {}

  def __str__(self):
    return f"{self.name}:{self.attack}/{self.health}"

  def copy(self):
    new_pet = Pet(self.name, self.attack, self.health)
    new_pet.level = self.level
    new_pet.merged_count = self.merged_count
    new_pet.triggers = self.triggers
    return new_pet


class Ant(Pet):
  def __init__(self):
    super().__init__("Ant", 2, 1)
    self.triggers["feint"] = ("boost", "random_friend", 1, 2, 1)

class Beaver(Pet):
  def __init__(self):
    super().__init__("Beaver", 2, 2)
    self.triggers["sell"] = ("boost", "random_friend", 2, 0, 2)

class Cricket(Pet):
  def __init__(self):
    super().__init__("Cricket", 1, 2)
    self.triggers["feint"] = ("summon", CricketToken)

class Duck(Pet):
  def __init__(self):
    super().__init__("Duck", 1, 2)
    self.triggers["sell"] = ("boost", "all_shop", None, 1, 2)

class Fish(Pet):
  def __init__(self):
    super().__init__("Fish", 2, 3)
    self.triggers["level_up"] = ("boost", "all_friends", None, 1, 1)

class Horse(Pet):
  def __init__(self):
    super().__init__("Horse", 1, 1)
    self.triggers["friend_summon"] = ("boost", "trigger", None, 1, 0)

class Mosquito(Pet):
  def __init__(self):
    super().__init__("Mosquito", 2, 2)
    self.triggers["start_battle"] = ("damage", "random_enemy", 1, 1)

class Otter(Pet):
  def __init__(self):
    super().__init__("Otter", 1, 2)
    self.triggers["buy"] = ("boost", "random_friend", 1, 1, 1)

class Pig(Pet):
  def __init__(self):
    super().__init__("Pig", 2, 2)
    self.triggers["sell"] = ("gold", +1)

class Sloth(Pet):
  def __init__(self):
    super().__init__("Sloth", 1, 1)

all_pet_classes = [Ant, Beaver, Cricket, Duck, Fish,
                   Horse, Mosquito, Otter, Pig, Sloth]


# Tokens
class CricketToken(Pet):
  def __init__(self):
    super().__init__("CricketToken", 1, 1)
