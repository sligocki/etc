# Compute ngram letter frequencies in wordlist.

import argparse
import collections
from pathlib import Path

import pandas as pd


def ngram_count(words, n : int) -> collections.Counter:
  ngrams = collections.Counter()
  for word in words:
    for i in range(len(word) - n):
      ngrams[word[i:i+n]] += 1
  return ngrams

def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("in_wordlist_csv", type=Path)
  parser.add_argument("--max-size", type=int, default=6)
  args = parser.parse_args()

  df = pd.read_csv(args.in_wordlist_csv)
  lemmas = df.lemma

  for n in range(1, args.max_size):
    print(f"{n}-grams frequencies:")
    ngrams = ngram_count(lemmas, n)
    total = ngrams.total()
    for i, (ngram, count) in enumerate(ngrams.most_common(40)):
      print(f"  {i:3d}: {ngram}  {count / total:6.2%}")
    print()


if __name__ == "__main__":
  main()
