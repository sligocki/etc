import argparse

import bf_enum
import bf_sim


def sim_all(size, steps_cutoff):
  num_total = 0
  num_unk = 0
  num_halt = 0
  total_steps = 0

  max_steps = -1
  best_steps_prog = None
  max_score = -1
  best_score_prog = None
  for prog in bf_enum.bf_enum(size):
    sim = bf_sim.BFSim(prog)
    sim.run(steps_cutoff)
    num_total += 1
    total_steps += sim.num_steps
    if sim.is_running():
      num_unk += 1
    else:
      # Halted
      num_halt += 1
      if sim.num_steps > max_steps:
        max_steps = sim.num_steps
        best_steps_prog = prog
      if sim.score() > max_score:
        max_score = sim.score()
        best_score_prog = prog

  print(f"Simulated all {num_total:_} BFs of size {size} for {steps_cutoff:_} steps:")
  print(f" * Total steps: {total_steps:_} (Mean: {total_steps / num_total:_.0f})")
  print(f" * Halted {num_halt:_} / {num_total:_} = {num_halt/num_total:.1%}")
  print(f" * Max score: {max_score:_} {best_score_prog}")
  print(f" * Max steps: {max_steps:_} {best_steps_prog}")


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("size", type=int)
  parser.add_argument("steps_cutoff", type=int)
  args = parser.parse_args()

  sim_all(args.size, args.steps_cutoff)

if __name__ == "__main__":
  main()
