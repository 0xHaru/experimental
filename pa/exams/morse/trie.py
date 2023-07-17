class Node:
    def __init__(self, morse, letter):
        self.morse = morse
        self.letter = letter
        self.left = None  # self.left.morse is always gonna be a "."
        self.right = None  # self.right.morse is always gonna be a "-"

    def __repr__(self):
        return f"Node({self.morse}, {self.letter})"


class MorseTrie:
    def __init__(self, morse_codes, letters):
        self.root = Node("", "")

        # sorted() is REALLY important here because _insert()
        # doest NOT support "random" insertions.
        # We can only build the trie gradually!
        for morse_code, letter in sorted(zip(morse_codes, letters), key=lambda x: x[0]):
            self._insert(morse_code, letter)

    # Simple but VERY fragile implementation
    def _insert(self, morse_code, letter):
        node = self.root

        for morse in morse_code:
            branch = "left" if morse == "." else "right"

            if node.__dict__[branch]:
                node = node.__dict__[branch]
            else:
                node.__dict__[branch] = Node(morse, letter)

    def decode(self, morse_code):
        node = self.root

        for morse in morse_code:
            branch = "left" if morse == "." else "right"
            node = node.__dict__[branch]

        return node.letter
