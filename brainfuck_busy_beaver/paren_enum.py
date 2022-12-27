import argparse

def paren_enum(size):
  """Enumerate strings in the alphabet "[]." with matching parens."""
  if size == 0:
    yield ""
  else:
    # 1) All strings ending in .
    for prefix in paren_enum(size - 1):
      yield prefix + "."
    # 2) All strings ending in ]
    if size >= 2:
      for loop_len in range((size - 2) + 1):
        prefix_len = size - 2 - loop_len
        for prefix in paren_enum(prefix_len):
          for loop in paren_enum(loop_len):
            yield prefix + "[" + loop + "]"



def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("max_size", type=int)
  args = parser.parse_args()

  for size in range(args.max_size + 1):
    total_count = sum(1 for prog in paren_enum(size))
    print(f"Size {size:4d} / Total {total_count:11_d}")

if __name__ == "__main__":
  main()
