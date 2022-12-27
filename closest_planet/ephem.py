# Calculate closest planets using JPL Ephemeris.

import argparse
import collections
import math
import random

import skyfield
from skyfield.api import load

kPlanetNames = ["mercury", "venus", "earth",
                "mars barycenter",
                "jupiter barycenter", "saturn barycenter",
                "uranus barycenter", "neptune barycenter",
                "pluto barycenter"]

def load_planets(duration : str):
  if duration == "s":
    # Years: 1849-2150
    return load('de440s.bsp')
  elif duration == "m":
    # Years: 1550-2650
    return load('de440.bsp')
  else:
    # Years: -13,200 to 17,191
    return load('de441.bsp')

def random_times(start, end, num_samples):
  return [random.uniform(start, end) for _ in range(num_samples)]

def closest_planet(planets, source_name, time):
  """Return closest planet to source at given time."""
  source = planets[source_name]
  min_dist = math.inf
  closest = None
  for dest_name in kPlanetNames:
    if dest_name != source_name:
      dest = planets[dest_name]
      # NOTE: We measure the distance between two objects using Barycentric
      # positions (not Astrometric or Apparent positions which have to do with
      # adjusting for observation from Earth).
      distance = (dest.at(time) - source.at(time)).distance().au
      if distance < min_dist:
        min_dist = distance
        closest = dest_name
  return closest, min_dist

def closest_over_time(planets, source_name, times):
  closests = collections.Counter()
  for t in times:
    neighbor, dist = closest_planet(planets, source_name, t)
    closests[neighbor] += 1
  return closests

def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("source", choices=kPlanetNames)
  parser.add_argument("num_samples", type=int)
  args = parser.parse_args()

  planets = load_planets("l")
  ts = load.timescale()
  times = random_times(ts.tdb(1970), ts.tdb(17_191), args.num_samples)
  closests = closest_over_time(planets, args.source, times)
  for name in sorted(closests, key=lambda x: closests[x], reverse=True):
    print(f"{name:20s} : {closests[name] / args.num_samples:.3%}")

main()
