class Node:
    def __init__(self, key):
        self.key = key
        self.neighbors = []

    def add_neighbor(self, node):
        assert isinstance(node, Node)
        self.neighbors.append(node)

    def __repr__(self):
        return f"Node({self.key})"


class Graph:
    def __init__(self, nodes):
        self.nodes = [Node(n) for n in nodes]

    def find(self, key):
        for node in self.nodes:
            if key == node.key:
                return node
        return None

    def add_node(self, key):
        self.nodes.append(Node(key))

    def add_edge(self, from_, to):
        _from = self.find(from_)
        _to = self.find(to)

        if _from and _to:
            _from.add_neighbor(_to)
            _to.add_neighbor(_from)
        else:
            raise Exception("One or more nodes were not found")

    def _dfs(self, root, func, visited):
        visited.add(root)
        func(root)

        for neighbor in root.neighbors:
            if neighbor not in visited:
                self._dfs(neighbor, func, visited)

    def dfs(self, root, func):
        self._dfs(root, func, set())


graph = Graph([1, 2, 3, 4])
graph.add_edge(1, 2)
graph.add_edge(1, 3)
graph.add_edge(2, 4)
graph.add_edge(3, 4)
graph.dfs(graph.find(1), print)
