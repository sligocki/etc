# Extract wordlist from Tezaurs LMF/XML.

import argparse
import csv
from pathlib import Path

from lxml import etree


def parse_tag(tag) -> str | None:
  if tag is not None:
    tag = tag.text
    # Remove all text after ":" so that verb-1r:veik;veic;veic -> verb-1r
    if ":" in tag:
      tag = tag[:tag.find(":")]
  return tag

def main():
  parser = argparse.ArgumentParser()
  parser.add_argument("in_lmf_xml", type=Path)
  parser.add_argument("out_csv", type=Path)
  args = parser.parse_args()

  with open(args.in_lmf_xml) as infile:
    tree = etree.parse(infile)
  root = tree.getroot()

  with open(args.out_csv, "w") as outfile:
    writer = csv.DictWriter(outfile, ["lemma", "pos", "tag"])
    writer.writeheader()

    for entry in root.find("Lexicon").findall("LexicalEntry"):
      lemma = entry.find("Lemma")
      tag = entry.find("Tag")
      writer.writerow({
        "lemma": lemma.get("writtenForm"),
        "pos": lemma.get("partOfSpeech"),
        "tag": parse_tag(tag),
      })

if __name__ == "__main__":
  main()
