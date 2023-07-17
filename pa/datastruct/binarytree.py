class Node:
    def __init__(self, data, left=None, right=None):
        self.data = data
        self.left = left
        self.right = right

    def find(self, node):
        assert isinstance(node, Node)

        if self.data == node.data:
            return self

        if self.left:
            if n := self.left.find(node):
                return n

        if self.right:
            if n := self.right.find(node):
                return n

        return None

    def preorder(self, func):
        func(self)

        if self.left:
            self.left.preorder(func)

        if self.right:
            self.right.preorder(func)

    def __repr__(self):
        return f"Node({self.data})"


root = Node(1, Node(2,
                    Node(4),
                    Node(5)),
               Node(3,
                    Node(6)))

node = root.find(Node(3))
node.right = Node(7)

root.preorder(print)

# Links:
# https://stackoverflow.com/questions/2598437/how-to-implement-a-binary-tree
# https://stackoverflow.com/questions/2358045/how-can-i-implement-a-tree-in-python
# https://stackoverflow.com/questions/2482602/a-general-tree-implementation
# https://stackoverflow.com/questions/18047634/finding-a-node-in-a-tree-using-recursion-in-python
