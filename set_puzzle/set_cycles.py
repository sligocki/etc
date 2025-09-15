
def s(a, b):
  """For attribute values |a| and |b|, find 3rd matching attribute value."""
  assert a in [0, 1, 2] and b in [0, 1, 2], (a, b)
  if a == b:
    # If same, 3rd is also same.
    return a
  else:
    # If different, 3rd is other different option (a + b + c = 3)
    return 3 - a - b

def mc(x, y):
  """Find 3rd card which makes a set with cards |x| and |y|."""
  assert len(x) == len(y)
  ret = []
  for a, b in zip(x, y):
    ret.append(s(a, b))
  return tuple(ret)


def
