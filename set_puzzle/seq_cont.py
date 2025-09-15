import itertools

def s(a, b):
  assert a in [0, 1, 2] and b in [0, 1, 2], (a, b)
  if a == b:
    return a
  else:
    return 3 - a - b

def seq_cont(xs):
  n = len(xs)
  seen = set()
  seen.add(tuple(xs))
  for i in itertools.count():
    xs.append(s(xs[i], xs[i+1]))
    last = tuple(xs[-n:])
    if last in seen:
      return xs, seen
    else:
      seen.add(last)

def norm(xs):
  ys = []
  nmap = {}
  for x in xs:
    if x not in nmap:
      nmap[x] = len(nmap)
    ys.append(nmap[x])
  return tuple(ys)


def main():
  for n in range(2, 21):
    init = [0] * (n-1) + [1]
    seq, seen = seq_cont(init)
    nseen = {norm(xs) for xs in seen}
    print(n, len(seen), len(nseen))

main()
