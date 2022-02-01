import argparse


def cross(m4, n4, k4, l4):
  A = m4**2 + n4**2 - k4**2 - l4**2
  B = -2 * (m4 + n4 - k4 - l4)

  m1 = A + m4 * B
  n1 = A + n4 * B
  m2 = A + k4 * B
  n2 = A + l4 * B

  print(f"{m1=} {n1=} {m2=} {n2=}")
  print()

  e = m1**2 + n1**2
  assert e == m2**2 + n2**2

  a = e - 2 * m1 * (m1 + n1)
  j = e - 2 * n1 * (m1 + n1)
  c = e - 2 * m2 * (m2 + n2)
  g = e - 2 * n2 * (m2 + n2)

  print(f"{a:20_d} {'':20} {c:20_d}")
  print(f"{'':20} {e:20_d} {'':20}")
  print(f"{g:20_d} {'':20} {j:20_d}")
  print()
  print(f"{a**2:20_d} {'':20} {c**2:20_d}")
  print(f"{'':20} {e**2:20_d} {'':20}")
  print(f"{g**2:20_d} {'':20} {j**2:20_d}")
  print()
  print(f"{a**2 + e**2 + j**2=}")
  print(f"{c**2 + e**2 + g**2=}")
  print(f"{3 * e**2=}")

def angle(m5, n5, k5, l5, p5):
  A = m5**2 + n5**2 - k5**2 - l5**2 - p5**2
  B = -2 * (m5 + 5 * n5 - k5 - 3 * l5 - 4 * p5)

  m1 =     A + m5 * B
  n1 = 5 * A + n5 * B
  m3 =     A + k5 * B
  n3 = 3 * A + l5 * B
  k3 = 4 * A + p5 * B

  print(f"{m1=} {n1=} {m3=} {n3=} {k3=}")
  print()

  e = m1**2 + n1**2
  assert e == m3**2 + n3**2 + k3**2

  a = e - 2 * m1 * (m1 + n1)
  j = e - 2 * n1 * (m1 + n1)
  a2 = e - 2 * m3 * (m3 + n3 + k3)
  c = e - 2 * n3 * (m3 + n3 + k3)
  b = e - 2 * k3 * (m3 + n3 + k3)
  
  print(f"{a=} {a2=}")
  print()

  print(f"{a:20_d} {b:20_d} {c:20_d}")
  print(f"{'':20} {e:20_d} {'':20}")
  print(f"{'':20} {'':20} {j:20_d}")
  print()
  print(f"{a**2:20_d} {b**2:20_d} {c**2:20_d}")
  print(f"{'':20} {e**2:20_d} {'':20}")
  print(f"{'':20} {'':20} {j**2:20_d}")
  print()
  print(f"{a**2 + e**2 + j**2=}")
  print(f"{a2**2 + b**2 + c**2=}")
  print(f"{3 * e**2=}")


parser = argparse.ArgumentParser()
parser.add_argument("--cross", type=int, nargs=4)
parser.add_argument("--angle", type=int, nargs=5)
args = parser.parse_args()

if args.cross:
  cross(*args.cross)
if args.angle:
  angle(*args.angle)
