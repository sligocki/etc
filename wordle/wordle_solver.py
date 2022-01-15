import collections

def load_words():
  words = set()
  with open("words_accepted.txt", "r") as f:
    for line in f:
      words.add(line.strip())
  return words

kBlank = 0
kYellow = 1
kGreen = 2
def feedback(guess, answer):
  ans_counts = collections.Counter(answer)
  colors = [kBlank for _ in range(len(answer))]
  # Assign Greens
  for i in range(len(answer)):
    if guess[i] == answer[i]:
      colors[i] = kGreen
      ans_counts[guess[i]] -= 1
  # Assign Yellows
  for i in range(len(answer)):
    if colors[i] == kBlank:
      if ans_counts[guess[i]] > 0:
        colors[i] = kYellow
        ans_counts[guess[i]] -= 1
  return colors


# A coule tests
print(feedback("yabbe", "abbey"))
