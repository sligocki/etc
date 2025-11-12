from collections import Counter
from fractions import Fraction


_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

def prime_factor(n: int) -> list[int]:
  counts = Counter[int]()
  i = 0
  while n > 1:
    p = _primes[i]
    if n % p == 0:
      n //= p
      counts[i] += 1
    else:
      i += 1
  return [counts[i] for i in range(max(counts.keys(), default=0) + 1)]

def factors_to_frac(factors: list[int]) -> Fraction:
  val = Fraction(1)
  for k, count in enumerate(factors):
    if count > 0:
      val *= _primes[k]**count
    if count < 0:
      val /= _primes[k]**(-count)
  return val

def factors_to_int(factors: list[int]) -> int:
  val = factors_to_frac(factors)
  assert val.is_integer(), (factors, val)
  return int(val)
