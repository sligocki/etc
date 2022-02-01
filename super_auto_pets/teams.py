import pets


# TODO: Make this way smarter!
class Team(list):
  def __init__(self, pets_list):
    super().__init__(pets_list)
    
  def __str__(self):
    return "_".join(str(pet) for pet in self)

  def copy(self):
    return Team([pet.copy() for pet in self])


def example_teams():
  team_FFF = Team([pets.Fish(), pets.Fish(), pets.Fish()])
  team_MAC = Team([pets.Mosquito(), pets.Ant(), pets.Cricket()])
  team_FAF = Team([pets.Fish(), pets.Ant(), pets.Fish()])
  team_MMF = Team([pets.Mosquito(), pets.Mosquito(), pets.Fish()])

  def horse_boost(pet):
    pet.attack += 1
    return pet
  team_CCH = Team([horse_boost(pets.Cricket()),
                   horse_boost(pets.Cricket()),
                   pets.Horse()])
  team_CAH = Team([horse_boost(pets.Cricket()),
                   horse_boost(pets.Ant()),
                   pets.Horse()])

  def duck_boost(pet):
    pet.attack += 1
    pet.health += 1
    return pet
  team_dFF = Team([duck_boost(pets.Fish()), duck_boost(pets.Fish())])
  team_dCC = Team([duck_boost(pets.Cricket()), duck_boost(pets.Cricket())])

  return [team_FFF, team_MAC, team_FAF, #team_MMF,
          team_CCH, team_CAH, team_dFF, team_dCC]
