import java.util.ArrayList;
import java.util.List;

/**
 * Binary string tree node implementation
 */
public class StringNode {
    private String data;
    private StringNode parent;
    private StringNode left;
    private StringNode right;

    public StringNode(String data) {
        this.data = data;
    }

    public StringNode addLeftChild(String data) {
        StringNode child = new StringNode(data);
        child.parent = this;
        left = child;
        return child;
    }

    public StringNode addRightChild(String data) {
        StringNode child = new StringNode(data);
        child.parent = this;
        right = child;
        return child;
    }

    public List<String> preorder() {
        List<String> visited = new ArrayList<>();
        visited.add(data);

        if(this.left != null)
            visited.addAll(this.left.preorder());

        if(this.right != null)
            visited.addAll(this.right.preorder());

        return visited;
    }

    public List<String> inorder() {
        List<String> visited = new ArrayList<>();

        if(this.left != null)
            visited.addAll(this.left.inorder());

        visited.add(data);

        if(this.right != null)
            visited.addAll(this.right.inorder());

        return visited;
    }

    public List<String> postorder() {
        List<String> visited = new ArrayList<>();

        if(this.left != null)
            visited.addAll(this.left.postorder());

        if(this.right != null)
            visited.addAll(this.right.postorder());

        visited.add(data);
        return visited;
    }

    public static void main(String[] args) {
        StringNode root = new StringNode("0");
        {
            StringNode node1 = root.addLeftChild("1");
            StringNode node2 = root.addRightChild("2");
            {
                node1.addLeftChild("4");
                node1.addRightChild("5");
                StringNode node21 = node2.addLeftChild("6");
                {
                    node21.addRightChild("7");
                }
            }
        }

        System.out.println(root.preorder());
        System.out.println(root.inorder());
        System.out.println(root.postorder());
    }
}
