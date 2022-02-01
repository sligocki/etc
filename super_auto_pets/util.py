
import datetime
import sys


def log(*messages):
  print(f"{datetime.datetime.now().isoformat()} ", *messages, file=sys.stderr)
  sys.stderr.flush()


def argsort(xs, reverse=False, key=None):
  sub_key = None
  if key:
    sub_key = lambda ix: key(ix[1])
  return [i for i, x in sorted(enumerate(xs), reverse=reverse, key=sub_key)]


def cartesian_product(vals, num):
  """Yield all sequences of size num with values in vals as entries."""
  if num == 0:
    yield []
    return
  for seq in cartesian_product(vals, num - 1):
    for val in vals:
      yield [val] + seq
