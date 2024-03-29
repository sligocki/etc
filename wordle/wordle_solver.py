import collections
import math
import time


def load(type):
  words = set()
  with open(f"words_{type}.txt", "r") as f:
    for line in f:
      words.add(line.strip())
  return words

def load_dict():
  return load("accepted")
def load_answers():
  return load("answers")


kBlank = 0
kYellow = 1
kGreen = 2
def evaulate_guess(guess, answer):
  ans_counts = collections.Counter(answer)
  feedback = [kBlank for _ in range(len(answer))]
  # Assign Greens
  for i in range(len(answer)):
    if guess[i] == answer[i]:
      feedback[i] = kGreen
      ans_counts[guess[i]] -= 1
  # Assign Yellows
  for i in range(len(answer)):
    if feedback[i] == kBlank:
      if ans_counts[guess[i]] > 0:
        feedback[i] = kYellow
        ans_counts[guess[i]] -= 1
  return tuple(feedback)

# Top results:
#   ORATE, ROATE, OATER : 1.7892
#   REALO               : 1.7810
#   TALER, RATEL, ARTEL : 1.7784
#   TERAI, RETIA        : 1.7780
#   ARIEL, RAILE        : 1.7698
def first_word_max_colors(all_words, answers):
  mean_colors = {}
  for i, first_guess in enumerate(all_words):
    total_colors = 0
    for ans in answers:
      feedback = evaulate_guess(first_guess, ans)
      # Weight all colors (Yellow or Green) equally in this function.
      num_color = sum(1 for color in feedback if color != kBlank)
      total_colors += num_color
    mean_colors[first_guess] = total_colors / len(answers)
    if i % 1000 == 0:
      print(i, first_guess, mean_colors[first_guess])
  score_word = [(score, word) for (word, score) in mean_colors.items()]
  score_word.sort(reverse=True)
  print(score_word[:10])

def categorize_by_feedback(guess, answers):
  feedback_answers = collections.defaultdict(set)
  for answer in answers:
    feedback = evaulate_guess(guess, answer)
    feedback_answers[feedback].add(answer)
  return feedback_answers

def max_category(categories):
  big_key = None
  big_category = None
  max_size = -1
  for key, category in categories.items():
    if len(category) > max_size:
      big_key = key
      big_category = category
      max_size = len(big_category)
  return big_key, big_category

def min_category(categories):
  small_key = None
  small_category = None
  min_size = math.inf
  for key, category in categories.items():
    if len(category) < min_size:
      small_key = key
      small_category = category
      min_size = len(small_category)
  return small_key, small_category

# Top results:
#   AESIR, REAIS, SERAI : 168
#   AYRIE               : 171
#   ARIEL, RAILE        : 173
#   ALOES               : 174
#   REALO               : 176
#   STOAE               : 177
def max_categories(all_words, answers):
  biggest_categories = {}
  for i, guess in enumerate(all_words):
    feedback_answers = categorize_by_feedback(guess, answers)
    biggest_categories[guess] = max_category(feedback_answers)
    if i % 1000 == 0:
      print(" ...", i, guess, len(biggest_categories[guess]), time.process_time())
  return biggest_categories

def min_max_categories(all_words, answers):
  big_categories = max_categories(all_words, answers)
  best_guess, category = min_category({guess: cat for (guess, (_, cat)) in big_categories.items()})
  return best_guess, big_categories[best_guess][0], category

def iterate_min_max_categories(all_words, answers):
  remaining_answers = answers
  while len(remaining_answers) > 1:
    optimal_guess, worst_response, category = min_max_categories(all_words, remaining_answers)
    print(f"{optimal_guess:10s} {worst_response} {len(category):6_d}")
    remaining_answers = category


# A coule tests
#print(evaulate_guess("yabbe", "abbey"))
all_words = load_dict()
answers = load_answers()
#first_word_max_colors(all_words, answers)
#min_max_categories(all_words, answers)
iterate_min_max_categories(all_words, answers)
