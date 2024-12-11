"""
This is code for simulating a game that Daniel Yuan proposed on the bbchallenge Discord:
https://discord.com/channels/960643023006490684/960643023530762343/1315800314070437979

Each player starts with cards numbered 1 to n. Each turn they simultaneously pick a card to play.
If Alice plays a higher card than Bob, then Alice discards her card and takes Bob's into her hand.
If both play the same value card, both discard. Repeat. First player who runs out of cards loses.
"""

from __future__ import annotations

from dataclasses import dataclass
# from fractions import Fraction
import functools
from typing import Iterable, Iterator

import nashpy
import numpy as np


# Types
Card = int
Value = np.float64

@dataclass(frozen=True)
class Hand:
  """A collection of cards "in hand" for one player. May include multiple of some cards."""
  data : tuple

  def __init__(self, data : Iterable[Card]):
    object.__setattr__(self, 'data', tuple(sorted(data)))

  def add(self, card : Card) -> Hand:
    return Hand(self.data + (card,))

  def remove(self, card : Card) -> Hand:
    hand = list(self.data)
    # Will raise error if card not in hand.
    hand.remove(card)
    return Hand(hand)
  
  def unique_cards(self) -> Iterator[Card]:
    """Iterate through cards, but only one of each value."""
    for card in sorted(set(self.data)):
      yield card

@dataclass(frozen=True)
class Move:
  """A move or play made by both players in one turn."""
  card1 : Card
  card2 : Card

@dataclass(frozen=True)
class State:
  """Current board state (both players hands)."""
  hand1 : Hand
  hand2 : Hand

  def enum_moves(self) -> Iterator[Move]:
    """Enumerate all possible moves from this position."""
    for card1 in self.hand1.unique_cards():
      for card2 in self.hand2.unique_cards():
        yield Move(card1, card2)


def play(state : State, move : Move) -> State:
  """Resolve playing one turn, update and remove hands."""
  hand1 = state.hand1.remove(move.card1)
  hand2 = state.hand2.remove(move.card2)
  if move.card1 > move.card2:
    hand1 = hand1.add(move.card2)
  if move.card2 > move.card1:
    hand2 = hand2.add(move.card1)
  return State(hand1, hand2)


Strategy = np.array # array of Value

@dataclass(frozen=True)
class StrategyNode:
  value : Value
  game : nashpy.Game | None = None
  strat1 : Strategy | None = None
  strat2 : Strategy | None = None


@functools.cache
def evaluate(state : State) -> StrategyNode:
  # All possible moves/cards for each player.
  moves1 = list(state.hand1.unique_cards())
  moves2 = list(state.hand2.unique_cards())

  # Game over
  if not moves1 and not moves2:
    # Draw
    return StrategyNode(Value(0))
  if not moves1:
    # Player 2 wins
    return StrategyNode(Value(-1))
  if not moves2:
    # Player 1 wins
    return StrategyNode(Value(1))

  # We must go deeper

  # Recursively evaluate all moves from this state and create a utility matrix.
  # Utility matrix. util[card1][card2] = payout for player 1 when playing that move.
  util = [[evaluate(play(state, Move(card1, card2))).value
           for card2 in moves2]
          for card1 in moves1]
  game = nashpy.Game(np.array(util))

  # Since this is a zero-sum game, there is only one Nash equilibrium and it is the minimax result.
  best_strat1, best_strat2 = list(game.linear_program())

  # We ignore payout for player 2 which is just -payout1
  payout1 : Value = game[best_strat1, best_strat2][0]

  # print()
  # print(state)
  # print(util)
  # print(game)
  # print(nash_eq)
  # print(payout1)
  # print()

  return StrategyNode(payout1, game, best_strat1, best_strat2)


def full_game(n : int) -> StrategyNode:
  start_state = State(Hand(range(n)), Hand(range(n)))
  return evaluate(start_state)

for n in range(11):
  print(n, full_game(n))