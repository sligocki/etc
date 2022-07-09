import argparse


def bf_enum(size):
  """Enumerate all BF programs of size `size`."""
  if size == 0:
    yield ""
  else:
    # First enumerate all programs that end in a non-] instruction.
    for prefix in bf_enum(size - 1):
      for i in "+-><":
        yield prefix + i
    # Second enumerate all programs which end in a [] loop.
    if size >= 2:
      for loop_len in range((size - 2) + 1):
        prefix_len = size - 2 - loop_len
        for prefix in bf_enum(prefix_len):
          for loop in bf_enum(loop_len):
            yield prefix + "[" + loop + "]"

# Optimization: Don't allow wasted pairs of instructinos:
kSimpleInstr = {
  "+" : "+><",  # No +-
  "-" : "-><",  # No -+
  ">" : "+->",  # No ><
  "<" : "+-<",  # No <>
}
def simple_instr_opt(prev):
  if prev and prev[-1] in kSimpleInstr:
    return kSimpleInstr[prev[-1]]
  return "+-><"

def _bf_enum_opt_help(size, *, allow_end_loop=True, only_end_loop=False):
  """Optimized version of bf_enum, avoids certain unhelpful patterns."""
  if size == 0:
    yield ""
  else:
    # First enumerate all programs which end in a [] loop.
    if size >= 2 and allow_end_loop:
      # Optimization: Don't allow trivial loops (they never halt).
      max_loop_len = size - 2
      for loop_len in reversed(range(1, max_loop_len + 1)):
        prefix_len = size - 2 - loop_len
        for prefix in _bf_enum_opt_help(prefix_len):
          # Optimization: Do not allow ]]. If the inner loop ever runs, the
          # outer one will exit immediately, so the outer loop is pointless.
          for loop in _bf_enum_opt_help(loop_len, allow_end_loop = False):
            yield prefix + "[" + loop + "]"
    if not only_end_loop:
      # Second enumerate all programs that end in simple (non-]) instruction.
      for prefix in _bf_enum_opt_help(size - 1):
        for i in simple_instr_opt(prefix):
          yield prefix + i

def bf_enum_opt(size):
  # Optimization: Always end with ]. Any other ending is inefficient.
  # At least for num_steps, you could get the same value by starting with an equal number of >s.
  # For score, the obvious counterexample here is that +++ is max for small sizes ...
  # But even for score, I think there are more efficient ways to compute this in post-processing.
  for suffix in _bf_enum_opt_help(size - 1, only_end_loop = True):
    # Optimization: Always start with +. Any other starting symbol is inefficient.
    # At least for num_steps, - is symmetric with +. >< are a waste and [ will always fail first.
    yield "+" + suffix


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("--max-size", type=int, default=10)
  args = parser.parse_args()

  for size in range(1, args.max_size + 1):
    # All programs
    total_count = 0
    for prog in bf_enum(size):
      if args.verbose:
        print(prog)
      total_count += 1

    # Optimal enumeration
    opt_count = sum(1 for prog in bf_enum_opt(size))
    print(f"Size {size:4d} / Total {total_count:11_d} / Opt {opt_count:11_d}")

if __name__ == "__main__":
  main()
