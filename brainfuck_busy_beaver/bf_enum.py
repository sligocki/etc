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


def bf_enum_opt(size):
  """Optimized version of bf_enum, avoids certain unhelpful patterns."""
  if size == 0:
    yield ""
  else:
    # First enumerate all programs that end in a non-] instruction.
    for prefix in bf_enum_opt(size - 1):
      for i in "+-><":
        yield prefix + i
    # Second enumerate all programs which end in a [] loop.
    if size >= 2:
      # Optimization: Don't allow trivial loops (they never halt).
      for loop_len in range(1, (size - 2) + 1):
        prefix_len = size - 2 - loop_len
        for prefix in bf_enum_opt(prefix_len):
          for loop in bf_enum_opt(loop_len):
            yield prefix + "[" + loop + "]"


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("size", type=int)
  parser.add_argument("--verbose", "-v", action="store_true")
  args = parser.parse_args()

  count = 0
  for prog in bf_enum(args.size):
    if args.verbose:
      print(prog)
    count += 1
  print("Total BF programs of size", args.size, ":", count)

if __name__ == "__main__":
  main()
