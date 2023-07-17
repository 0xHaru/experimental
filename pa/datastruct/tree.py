class Node:
    def __init__(self, data, children=None):
        self.data = data
        self.children = []

        if children:
            for child in children:
                assert isinstance(child, Node)
                self.add_child(child)

    def add_child(self, node):
        assert isinstance(node, Node)
        self.children.append(node)

    def find(self, node):
        assert isinstance(node, Node)

        if self.data == node.data:
            return self

        for child in self.children:
            if n := child.find(node):
                return n

        return None

    def dfs(self, func):
        func(self)

        for child in self.children:
            child.dfs(func)

    def __repr__(self):
        return f"Node({self.data})"


root = Node(1, [Node(2),
                Node(3),
                Node(4, [Node(5),
                         Node(6)])])

node = root.find(Node(4))
node.add_child(Node(7))

root.dfs(print)

# Links:
# https://stackoverflow.com/questions/2358045/how-can-i-implement-a-tree-in-python
# https://stackoverflow.com/questions/2482602/a-general-tree-implementation
# https://stackoverflow.com/questions/18047634/finding-a-node-in-a-tree-using-recursion-in-python
