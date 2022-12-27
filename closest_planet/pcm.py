# Calculate closest planets using PCM (Point Circle Method).
# https://physicstoday.scitation.org/do/10.1063/PT.6.3.20190312a/full/

import argparse
import collections
import math
import random


# Semi-major axis in AUs. From https://windows2universe.org/our_solar_system/planets_orbits_table.html
kPlanetRadiusAu = {
  # "sol": 0.,
  # "foo": 1.,
  # "bar": 2.,
  # "ref": 3.,
  "mercury":  0.3871,
  "venus":    0.7233,
  "earth":    1.0000,
  "mars":     1.5273,
  "jupiter":  5.2028,
  "saturn":   9.5388,
  "uranus":  19.1914,
  "neptune": 30.0611,

  # # Dwarf Planets
  # "ceres":     2.7660,
  "pluto":    39.5294,
  # "haumea":   43.335,
  # "makemake": 45.791,
  # "eris":     67.6681,
}

def polar2cart(r, theta):
  return (r * math.cos(theta), r * math.sin(theta))

def distance(p1, p2):
  (x1, y1) = p1
  (x2, y2) = p2
  return math.sqrt((x2-x1)**2 + (y2-y1)**2)

def random_orbital_positions():
  return {
    planet : polar2cart(kPlanetRadiusAu[planet], random.uniform(0, 2 * math.pi))
    for planet in kPlanetRadiusAu
  }

def closest_planet(source, locs):
  max_dist = math.inf
  closest = None
  for dest in locs:
    if dest != source:
      dist = distance(locs[source], locs[dest])
      if dist < max_dist:
        max_dist = dist
        closest = dest
  return closest

def sample_closest(source, num_samples):
  closests = collections.Counter()
  for _ in range(num_samples):
    locs = random_orbital_positions()
    neighbor = closest_planet(source, locs)
    closests[neighbor] += 1
  return closests

def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("source", choices=kPlanetRadiusAu.keys())
  parser.add_argument("num_samples", type=int)
  args = parser.parse_args()

  closests = sample_closest(args.source, args.num_samples)
  for name in sorted(closests, key=lambda x: closests[x], reverse=True):
    print(f"{name:20s} : {closests[name] / args.num_samples:.3%}")

main()
