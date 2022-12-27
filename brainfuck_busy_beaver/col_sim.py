# Simulate various "collatz-like" iterated functions.

import math


# Simulate +[-> +*(N+1) [-<]>]
# It turns out that this simulates the "Collatz-like" function:
#   f(2k) -> Halt(Nk)
#   f(2k-1) -> f(Nk)
# And for N = 2^m + 1 this iterates exactly m+2 times before halting.
def A_naive(N):
  x = 1
  while True:
    k, r = divmod(x, 2)
    if r == 0:
      return N * k
    else:
      x = N*(k+1)

def A_fast(m):
  N = 2**m + 1
  if N > 2:
    A = (N**(m+1) - 2**(m+1)) // (N - 2)
    return N * (A + 1) // 2


# Simulate +*(M+1) [> +*(N+1) [-<]>>]
#   Follows these rules:
#     Start -> [0, M+1*, 0...]   (@ first [ or matching ])
#     [0*] -> Halt
#   Impossible: all values are >=0 [b+1*, -(N+1), d, e] -> [b+1, 0, d, e*]
#     [0, b+1*, c] -> [0, b, c+N*]
#     [0, a+1, b+1*, c] -> [0, a, b*, c+N]
def B1(M, N):
  # Pos: [0, a, b*, c, 0...]
  a, b, c = 0, M+1, 0
  while b > 0:
    assert c >= 0, (a, b, c)
    if a == 0:
      a, b, c = b-1, c+N, 0
    else:
      assert a > 0, (a, b, c)
      a, b, c = a-1, b-1, c+N
  assert b == 0, (a, b, c)
  return max(a, c)

#   Let B(a, b) = [0, a, b*, 0...] on first > instruction (pointing to memory with b).
#     Start -> B(M, N)
#     B(b+k, b)   -> Halt(Nb)
#     B(a,   a+k) -> B(k-1, N (a+1))
def B2(M, N):
  a = M
  b = N
  while a < b:
    a, b = (b-a)-1, N * (a+1)
  L = a - b
  R = N * b
  return max(L, R)

def opt_B(max_size=100):
  max_score = 0
  best_params = []
  for size in range(13, max_size + 1):
    MpN = size - 11
    is_improved = False
    for M in range(MpN + 1):
      N = MpN - M
      score = B2(M, N)
      if score and score > max_score:
        max_score = score
        best_params = (size, M, N)
        is_improved = True
    if is_improved:
      size, M, N = best_params
      prog = "+" * (M+1) + "[>" + "+" * (N+1) + "[-<]>>]"
      assert len(prog) == size, prog
      print(f"Size {size:2d} / Params {M=:2d} {N=:2d} / Score = {max_score:20,d} / {prog}")


# Simulate +A[+B>+C>-D[<]>->]
def C1(A, B, C, D, *, verbose=False, max_iters=1_000):
  a, b, c = 0, A, 0
  iters = 0
  while b != 0:
    k = math.inf
    lim = None
    k_c, r_c = divmod(-c, C)
    if r_c == 0 and 0 < k_c < k:
      k = k_c
      lim = "c"
    k_b, r_b = divmod(-b, B)
    if r_b == 0 and 0 < k_b < k:
      k = k_b
      lim = "b"
    if 0 < a + 1 < k:
      k = a + 1
      lim = "a"

    if verbose:
      print("... C1", a, b, c, lim, k)

    if lim == "c":
      # -> [a-k, b+Bk, c + Ck = 0, -Dk - 1, 0*]
      return max(a-k, b + B*k)

    elif lim == "b":
      # -> [a-k, b + Bk = 0, c + Ck - 1, -Dk*]
      a, b, c = c + C*k - 1, -D * k, 0

    elif lim == "a":
      a, b, c = b + B*(a+1) - 1, c + C*(a+1), -D*(a+1)

    else:
      # Infinite
      return None

    iters += 1
    if iters > max_iters:
      return None
  assert b == 0, (a, b, c)
  return a

def opt_C(max_size=100):
  max_score = 0
  best_params = []
  for size in range(14, max_size + 1):
    par_sum = size - 10
    is_improved = False
    for A in range(1, par_sum - 2):
      for B in range(1, par_sum - A - 1):
        for C in range(1, par_sum - A - B):
          D = par_sum - A - B - C
          assert D >= 1, D
          score = C1(A, B, C, D)
          if score and score > max_score:
            max_score = score
            best_params = (size, A, B, C, D)
            is_improved = True
    if is_improved:
      size, A, B, C, D = best_params
      prog = ("+" * A +
              "[" +
              "+" * B +
              ">" +
              "+" * C +
              ">" +
              "-" * D +
              "[<]>->]")
      assert len(prog) == size, (prog, size)
      print(f"Size {size:2d} / Score = {max_score:,d} / {best_params} / {prog}")

# print(C1(2, 2, 1, 3, verbose = True))
# print(C1(1, 1, 1, 5, verbose = True))
# print(C1(1, 1, 3, 1))
# print(C1(1, 1, 5, 1))
# print(C1(1, 2, 5, 1))
# print()
# opt_C(50)


# Simulate +(A+1)[>+(B+1)>+(C+1)[-<]>>]
def D1(A, B, C, *, verbose=False, max_iters=1_000):
  a, b, c = 0, A+1, 0
  iter = 0
  while b > a:
    # a b* c -> 0 b-a* c+Ba Ca -> 0 b-(a+1) c+B(a+1)* C(a+1)
    a, b, c = b - (a+1), c + B*(a+1), C*(a+1)
    iter += 1
    if verbose:
      print("... D1", iter, a, b, c)
    if iter >= max_iters:
      return None

  assert b <= a
  # a b* c -> a-b 0* c+Bb Cb -> Halt
  return max(a - b, c + B*b, C*b)

def opt_D(max_size):
  max_score = 0
  best_params = []
  for size in range(14, max_size + 1):
    par_sum = size - 13
    is_improved = False
    for A in range(par_sum):
      for B in range(par_sum - A):
        C = par_sum - A - B
        assert C >= 1, (A, B, C)
        score = D1(A, B, C)
        if score and score > max_score:
          max_score = score
          best_params = (size, A, B, C)
          is_improved = True
    if is_improved:
      size, A, B, C = best_params
      prog = ("+" * (A+1) +
              "[>" +
              "+" * (B+1) +
              ">" +
              "+" * (C+1) +
              "[-<]>>]")
      assert len(prog) == size, (prog, size)
      print(f"Size {size:2d} / Score = {max_score:e} / {best_params} / {prog}")

print(D1(0, 1, 2, verbose = True))
print()
opt_D(50)
