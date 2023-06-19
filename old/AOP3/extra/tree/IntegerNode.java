import java.util.ArrayList;
import java.util.List;

/**
 * N-ary integer tree node implementation
 */
public class IntegerNode {
    private Integer data;
    private IntegerNode parent;
    private List<IntegerNode> children;

    public IntegerNode(Integer data) {
        this.data = data;
        this.children = new ArrayList<>();
    }

    public IntegerNode addChild(Integer data) {
        IntegerNode child = new IntegerNode(data);
        child.parent = this;
        this.children.add(child);
        return child;
    }

    public List<Integer> preorder() {
        List<Integer> visited = new ArrayList<>();
        visited.add(data);

        for (IntegerNode child : children)
            visited.addAll(child.preorder());

        return visited;
    }

    public static void main(String[] args) {
        IntegerNode root = new IntegerNode(0);
        {
            IntegerNode node1 = root.addChild(1);
            IntegerNode node2 = root.addChild(2);
            root.addChild(3);
            {
                node1.addChild(4);
                node1.addChild(5);
                IntegerNode node21 = node2.addChild(6);
                {
                    node21.addChild(7);
                }
            }
        }

        System.out.println(root.preorder());  // [0, 1, 4, 5, 2, 6, 7, 3]
    }
}
