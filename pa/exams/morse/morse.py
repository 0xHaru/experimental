from trie import MorseTrie

MORSE_CODES = [
    ".-",  # A
    "-...",  # B
    "-.-.",  # C
    "-..",  # D
    ".",  # E
    "..-.",  # F
    "--.",  # G
    "....",  # H
    "..",  # I
    ".---",  # J
    "-.-",  # K
    ".-..",  # L
    "--",  # M
    "-.",  # N
    "---",  # O
    ".--.",  # P
    "--.-",  # Q
    ".-.",  # R
    "...",  # S
    "-",  # T
    "..-",  # U
    "...-",  # V
    ".--",  # W
    "-..-",  # X
    "-.--",  # Y
    "--..",  # Z
]

LETTERS = [chr(i) for i in range(ord("a"), ord("z") + 1)]


class Morse:
    trie = MorseTrie(MORSE_CODES, LETTERS)

    def __init__(self):
        pass

    def encode(self, string):
        encoded = []

        for char in string:
            match char:
                case " ":
                    encoded.pop()
                    encoded.append(char)
                case _:
                    encoded.append(MORSE_CODES[ord(char) - ord("a")])
                    encoded.append("␣")

        encoded.pop()
        return "".join(encoded)

    def decode(self, morse_code):
        decoded = []

        for words in morse_code.split(" "):
            for letter in words.split("␣"):
                decoded.append(Morse.trie.decode(letter))
            decoded.append(" ")

        return "".join(decoded)


morse = Morse()


encoded = morse.encode("the quick brown fox jumps over the lazy dog")
# -␣....␣. --.-␣..-␣..␣-.-.␣-.- -...␣.-.␣---␣.--␣-. ..-.␣---␣-..- .---␣..-␣--␣.--.␣... ---␣...-␣.␣.-. -␣....␣. .-..␣.-␣--..␣-.-- -..␣---␣--.
print(encoded)

decoded = morse.decode(
    "-␣....␣. --.-␣..-␣..␣-.-.␣-.- -...␣.-.␣---␣.--␣-. ..-.␣---␣-..- .---␣..-␣--␣.--.␣... ---␣...-␣.␣.-. -␣....␣. .-..␣.-␣--..␣-.-- -..␣---␣--."
)
# the quick brown fox jumps over the lazy dog
print(decoded)
