# Minimal test for nashpy failure.

import nashpy
import numpy as np

A = np.array(
  [
    [0, -1, -1],
    [-3/7, -1/3, -5/7],
    [-5/7, 1/2, -1/3],
  ]
)

game = nashpy.Game(A)
nash_eq = list(game.linear_program())

print(game)
print(nash_eq)