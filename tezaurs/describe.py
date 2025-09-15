# Process some stats for the wordlist.

import argparse
from pathlib import Path

import pandas as pd


def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("in_wordlist_csv", type=Path)
  args = parser.parse_args()

  df = pd.read_csv(args.in_wordlist_csv)
  print(f"Total lemmas: {len(df):_d}")

  pos_counts = df.groupby("pos")["lemma"].agg("count").sort_values(ascending=False)
  print("By part of speech:")
  print(pos_counts)

  tag_counts = df.groupby("tag")["lemma"].agg("count").sort_values(ascending=False)
  print("By tag:")
  print(tag_counts)


if __name__ == "__main__":
  main()
