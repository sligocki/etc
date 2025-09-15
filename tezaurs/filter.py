# Filter down wordlist to remove phrases, abbreviations, foreign words, etc.

import argparse
from pathlib import Path

import pandas as pd


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("in_wordlist_csv", type=Path)
  parser.add_argument("out_wordlist_csv", type=Path)
  args = parser.parse_args()

  df = pd.read_csv(args.in_wordlist_csv)
  print(f"Loaded {len(df):_d} rows")

  # Remove any lemmas with non-letters (., parentheses, spaces, ...)
  df = df[df.lemma.str.fullmatch(f"[a-zāēīūčšžģķļņ]*")]
  # Remove phrases.
  df = df[df.pos != "u"]
  # Remove abbreviations and foreign words.
  df = df[~df.tag.isin(["abbr", "foreign"])]
  df.to_csv(args.out_wordlist_csv, index=False)
  print(f"Wrote {len(df):_d} rows")

if __name__ == "__main__":
  main()
