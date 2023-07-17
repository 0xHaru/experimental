import os

from ruzzle import Ruzzle

if __name__ == "__main__":
    base_path = os.path.dirname(os.path.abspath(__file__))
    words_path = f"{base_path}/words.txt"

    print(Ruzzle(words_path).solve(["walk", "moon", "hate", "rope"]))
    print(Ruzzle(words_path).solve(["abbr", "evia", "tion", "alba"]))
    print(Ruzzle(words_path).solve(["abse", "imtn", "nded", "ssen"]))
    print(Ruzzle(words_path).solve(["reca", "rwar", "aazp", "syon"]))
    print(Ruzzle(words_path).solve(["abst", "oime", "uesl", "snsp"]))
    print(Ruzzle(words_path).solve(["essx", "ndet", "sigh", "raen"]))
    print(Ruzzle(words_path).solve(["poap", "lkjh", "aswe", "jhnh"]))

# Run: python main.py
