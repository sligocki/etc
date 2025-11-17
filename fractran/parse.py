from pathlib import Path
import re

import numpy as np

from base import Rule, Program
from primes import prime_factor


def parse_fractions(prog_str: str) -> Program:
  rule_strs = prog_str.strip().removeprefix("[").removesuffix("]").split(",")
  fracs = []
  num_reg = 0
  for rule_str in rule_strs:
    p, q = rule_str.split("/")
    top = prime_factor(int(p))
    bot = prime_factor(int(q))
    fracs.append((top, bot))
    num_reg = max(num_reg, len(top), len(bot))
  prog = []
  for (top, bot) in fracs:
    prog.append(Rule.from_ratio(top, bot, num_reg))
  return Program(prog)

def parse_vectors(prog_str: str) -> Program:
  matches = re.findall("\[ *([-+0-9 ]*?) *\]", prog_str)
  rows = []
  max_width = 0
  for match in matches:
    if match:
      try:
        row = np.fromstring(match, dtype=int, sep=" ")
      except:
        print("Error parsing row:", match)
        raise
      max_width = max(max_width, row.size)
      rows.append(row)
  prog = []
  for row in rows:
    row.resize(max_width)
    prog.append(Rule(row))
  return Program(prog)

def parse_program(prog_str: str) -> Program:
  if "/" in prog_str:
    return parse_fractions(prog_str)
  else:
    return parse_vectors(prog_str)

def read_file(filename_record: str) -> str:
  if ":" in filename_record:
    filename, record_num = filename_record.split(":")
    filename = Path(filename)
    record_num = int(record_num)
  else:
    filename = Path(filename_record)
    record_num = None
  if not filename.exists():
    raise FileExistsError(filename)
  with open(filename, "r") as f:
    if record_num is not None:
      # TODO: This assumes 1 record per line, which is not "currently" true for vec format.
      return f.readlines()[record_num]
    else:
      return f.read()

def load_program(prog_or_filename: str) -> Program:
  if not prog_or_filename.startswith("["):
    prog_str = read_file(prog_or_filename)
  else:
    prog_str = str(prog_or_filename)

  return parse_program(prog_str)

def enum_programs(filename: Path):
  with open(filename, "r") as f:
    for line in f:
      yield parse_program(line)
