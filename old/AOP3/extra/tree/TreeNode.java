import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * N-ary generic tree node implementation
 */
public class TreeNode<T> {
    private T data;
    private TreeNode<T> parent;
    private List<TreeNode<T>> children;

    public TreeNode(T data) {
        this.data = data;
        this.children = new ArrayList<>();
    }

    public TreeNode<T> addChild(T data) {
        TreeNode<T> child = new TreeNode<>(data);
        child.parent = this;
        children.add(child);
        return child;
    }

    public List<T> preorder() {
        List<T> visited = new ArrayList<>();
        visited.add(data);

        for (TreeNode<T> child : children)
            visited.addAll(child.preorder());

        return visited;
    }

    public List<T> postorder() {
        List<T> visited = new ArrayList<>();

        for (TreeNode<T> child : children)
            visited.addAll(child.postorder());

        visited.add(data);
        return visited;
    }

    public String toString() {
        StringBuilder buffer = new StringBuilder();
        prettyPrint(buffer, "", "");
        return buffer.toString();
    }

    private void prettyPrint(StringBuilder buffer, String prefix, String childrenPrefix) {
        buffer.append(prefix);
        buffer.append(data);
        buffer.append("\n");

        Iterator<TreeNode<T>> it = children.iterator();

        while (it.hasNext()) {
            TreeNode<T> next = it.next();

            if (it.hasNext())
                next.prettyPrint(buffer, childrenPrefix + "├── ", childrenPrefix + "│   ");
            else
                next.prettyPrint(buffer, childrenPrefix + "└── ", childrenPrefix + "    ");
        }
    }
}

// Resources:
// https://stackoverflow.com/questions/3522454/how-to-implement-a-tree-data-structure-in-java
// https://stackoverflow.com/questions/4965335/how-to-print-binary-tree-diagram-in-java
//
// https://stackoverflow.com/questions/19330731/tree-implementation-in-java-root-parents-and-children
// https://www.educative.io/blog/data-structures-trees-java
