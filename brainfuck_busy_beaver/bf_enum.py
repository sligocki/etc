import argparse


def bf_enum(size):
  """Enumerate all BF programs of size `size`."""
  if size == 0:
    yield ""
  else:
    for sub in bf_enum(size - 1):
      for i in "+-><":
        yield sub + i
    if size >= 2:
      for sub in bf_enum(size - 2):
        yield "[" + sub + "]"


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
