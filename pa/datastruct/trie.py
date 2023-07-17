class TrieNode:
    def __init__(self, char):
        # The character stored in this node
        self.char = char

        # Whether this can be the end of a word
        self.is_word = False

        # A dictionary of child nodes
        # keys are characters, values are nodes
        self.children = {}


class Trie:
    def __init__(self):
        """
        The trie has at least the root node.
        The root node does not store any character
        """
        self.root = TrieNode("")

    def insert(self, word):
        """Insert a word into the trie"""

        node = self.root

        # Loop through each character in the word
        # Check if there is no child containing the character,
        # create a new child for the current node
        for char in word:
            if char in node.children:
                node = node.children[char]
            else:
                # If a character is not found,
                # create a new node in the trie
                new_node = TrieNode(char)
                node.children[char] = new_node
                node = new_node

        # Mark the end of a word
        node.is_word = True

    def contains(self, prefix):
        """Given a prefix returns True if it's stored in the trie, False otherwise"""

        node = self.root

        for char in prefix:
            if char in node.children:
                node = node.children[char]
            else:
                return False, False

        return True, node.is_word

trie = Trie()
trie.insert("apple")
trie.insert("banana")

print(trie.contains("appl"))
print(trie.contains("apple"))
print(trie.contains("ban"))
print(trie.contains("banana"))

# Links:
# https://albertauyeung.github.io/2020/06/15/python-trie.html
