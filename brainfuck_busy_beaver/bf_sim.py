import argparse
import collections


class BF_Format_Error(Exception):
  pass


def match_parens(s):
  stack = []
  match_locs = {}
  for i, c in enumerate(s):
    if c == "[":
      stack.append(i)
    elif c == "]":
      assert stack, s
      j = stack.pop()
      match_locs[i] = j
      match_locs[j] = i
  assert not stack, s
  return match_locs

def tape_str(tape, head_loc):
  parts = []
  tape[head_loc]
  for loc in range(min(tape.keys()), max(tape.keys()) + 1):
    if loc == head_loc:
      parts.append(f"({tape[loc]:2})")
    else:
      parts.append(f" {tape[loc]:2} ")
  return " ".join(parts)

class BFSim:
  def __init__(self, bf_prog: str):
    self.prog = bf_prog
    # Tape is a two-way infinite set of registers. Each holds an unbounded integer.
    self.tape = collections.defaultdict(int)
    # Tape location. Starts at 0.
    self.loc = 0
    # Instruction pointer. Starts at beginning of program.
    self.instr = 0

    # Pre-process prog to locate matching parentheses.
    self.jump_loc = match_parens(self.prog)

    # Stats
    self.num_steps = 0

  def is_running(self):
    return self.instr < len(self.prog)

  def score(self):
    return max(self.tape.values(), default=0)

  def run(self, steps, verbose=False):
    end_step = self.num_steps + steps
    while self.num_steps < end_step and self.is_running():
      if verbose:
        print(f"{self.num_steps:5_d} : {self.instr:3d} {self.prog[self.instr]} :  {tape_str(self.tape, self.loc)}")
      self.step()

  def step(self):
    if self.is_running():
      if self.prog[self.instr] == "+":
        self.tape[self.loc] += 1
      elif self.prog[self.instr] == "-":
        self.tape[self.loc] -= 1
      elif self.prog[self.instr] == ">":
        self.loc += 1
      elif self.prog[self.instr] == "<":
        self.loc -= 1
      elif self.prog[self.instr] == "[":
        if self.tape[self.loc] == 0:
          # Jump to closing ]. Then increment below will move out of loop.
          self.instr = self.jump_loc[self.instr]
      elif self.prog[self.instr] == "]":
        if self.tape[self.loc] != 0:
          # Jump to opening [. Then increment will move into loop.
          self.instr = self.jump_loc[self.instr]
      elif self.prog[self.instr] != ".":
        # Treat "." as no-op.
        raise BF_Format_Error(self.prog, self.instr)

      # Advance to next instruction.
      self.instr += 1
      self.num_steps += 1


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("bf_prog")
  parser.add_argument("num_steps", nargs="?", type=int, default=1_000_000)
  parser.add_argument("--verbose", "-v", action="store_true")
  args = parser.parse_args()

  sim = BFSim(args.bf_prog)
  sim.run(args.num_steps, args.verbose)
  if sim.is_running():
    print("Over steps")
  else:
    print("Halted")
  print(f"Program size: {len(args.bf_prog):_d}")
  print(f"Num steps: {sim.num_steps:_d}")
  print(f"Max register: {sim.score():_d}")
  print(f"Sum registers: {sum(sim.tape.values()):_d}")

if __name__ == "__main__":
  main()
