# Simulate various "collatz-like" iterated functions.


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

max_score = 0
best_params = []
for size in range(13, 100):
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
