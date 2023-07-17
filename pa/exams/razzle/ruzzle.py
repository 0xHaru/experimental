from trie import Trie


class Ruzzle:
    def __init__(self, english_words):
        self.trie = self._build_trie(english_words)
        self.graph = {}
        self.word_matrix = []
        self.ruzzles = []

    def _build_trie(self, path):
        with open(path) as f:
            raw = f.read().split("\n")
            words = [w for w in raw if 3 <= len(w) <= 16]

        trie = Trie()

        for w in words:
            trie.insert(w)

        return trie

    def _get_neighbors(self, x, y):
        neighbors = []
        neighbors.append((x + 1, y))
        neighbors.append((x, y + 1))
        neighbors.append((x - 1, y))
        neighbors.append((x, y - 1))

        return [(x, y) for (x, y) in neighbors if 0 <= x <= 3 and 0 <= y <= 3]

    def _dfs(self, root_node, curr_node, acc, visited):
        visited.add(curr_node)
        x, y = curr_node
        acc += self.word_matrix[x][y]

        is_prefix, is_word = self.trie.contains(acc)

        if not is_prefix:
            return False, curr_node

        # Different paths may build the same word
        if is_word and acc not in self.ruzzles:
            self.ruzzles.append(acc)

        for neighbor in self.graph.get(curr_node):
            if neighbor not in visited:
                _, former_next = self._dfs(root_node, neighbor, acc, visited)
                if former_next != root_node:
                    visited.discard(former_next)  # Backtrack

        return True, curr_node

    def solve(self, word_matrix):
        self.word_matrix = word_matrix

        for x in range(0, 4):
            for y in range(0, 4):
                self.graph[(x, y)] = self._get_neighbors(x, y)

        for node in self.graph:
            self._dfs(node, node, "", set())

        return sorted(self.ruzzles)
