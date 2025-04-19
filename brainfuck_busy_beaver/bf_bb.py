import argparse
import time

import bf_enum
import bf_sim


def sim_all(size, steps_cutoff, *,
            print_steps, progress_interval):
  start_time = time.time()
  num_total = 0
  num_unk = 0
  num_halt = 0
  total_steps = 0
  halt_steps = 0

  max_steps = -1
  best_steps_prog = None
  max_score = -1
  best_score_prog = None
  for prog in bf_enum.bf_enum_opt(size):
    if progress_interval and num_total % progress_interval == 0:
      print(f"... {num_total:11_d} BFs simulated. Current: {prog}  ({time.time() - start_time:_.0f}s)")
    sim = bf_sim.BFSim(prog)
    sim.run(steps_cutoff)
    num_total += 1
    total_steps += sim.num_steps
    if sim.is_running():
      num_unk += 1
    else:
      # Halted
      num_halt += 1
      halt_steps += sim.num_steps
      if sim.num_steps > max_steps:
        print("+++ New Best Steps:", sim.num_steps, prog)
        max_steps = sim.num_steps
        best_steps_prog = prog
      if sim.score() > max_score:
        print("*** New Best Score:", sim.score(), prog)
        max_score = sim.score()
        best_score_prog = prog
      if sim.num_steps > print_steps:
        print("  xxx  ", sim.num_steps, sim.score(), prog)

  print(f"Simulated {num_total:_} BFs of size {size} for {steps_cutoff:_} steps:")
  if num_total > 0:
    print(f" * Total steps: {total_steps:_} ({total_steps / (time.time() - start_time):_.0f} steps / s)")
    print(f" * Halted {num_halt:_} / {num_total:_} = {num_halt/num_total:.1%}")
    print(f" * Max score: {max_score:_} {best_score_prog}")
    print(f" * Steps: Max: {max_steps:_} {best_steps_prog}", end="")
    if num_halt > 0:
      print(f"  (Mean: {halt_steps / num_halt:_.0f})")


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("size", type=int)
  parser.add_argument("steps_cutoff", type=int)
  parser.add_argument("print_steps", type=int,
                      help="Print all machines above this many steps.")
  parser.add_argument("--progress-interval", "--progress", "-p",
                      type=int, default=0,
                      help="Print progress at this interval (0 means never).")
  args = parser.parse_args()

  sim_all(args.size, args.steps_cutoff,
          print_steps = args.print_steps,
          progress_interval = args.progress_interval)

if __name__ == "__main__":
  main()
