import java.util.ArrayList;
import java.util.Vector;

privileged public aspect UndoRedoAspect pertarget(matchCons()) {
    // PERTARGET POINTCUT //
    pointcut matchCons()
        : execution(public NaiveTextEditor.new(..));

    // TREE IMPLEMENTATION //
    private class Node {
        private Vector<Character> data;
        private Node parent;
        private ArrayList<Node> children;

        public Node(Vector<Character> data) {
            this.data = new Vector<Character>(data);
            children = new ArrayList<>();
        }

        public Node addChild(Vector<Character> data) {
            Node child = new Node(data);
            child.parent = this;
            children.add(child);
            return child;
        }

        public Vector<Character> getData() {
            return new Vector<Character>(data);
        }

        public Node getParent() {
            return parent;
        }

        public ArrayList<Node> getChildren() {
            return new ArrayList<Node>(children);
        }
    }

    // ASPECT STATE //
    private Node root = null;
    private Node current = null;

    // INTRODUCTIONS //
    declare parents : NaiveTextEditor implements UndoRedoInterface;

    public void NaiveTextEditor.undo() {}
    public void NaiveTextEditor.redo(int branch) {}

    private Vector<Character> NaiveTextEditor.getText() {
        return new Vector<Character>(text);
    }

    private void NaiveTextEditor.setText(Vector<Character> text) {
        this.text = new Vector<Character>(text);
    }

    // POINTCUTS //
    pointcut matchAddChar(NaiveTextEditor editor)
        : call(public void NaiveTextEditor.addChar(char)) &&
          target(editor);

    pointcut matchDelChar(NaiveTextEditor editor)
        : call(public char NaiveTextEditor.delChar()) &&
          target(editor);

    pointcut matchUndo(NaiveTextEditor editor)
        : call(public void NaiveTextEditor.undo()) &&
          target(editor);

    pointcut matchRedo(NaiveTextEditor editor, int branch)
        : call(public void NaiveTextEditor.redo(int)) &&
          target(editor) &&
          args(branch);

    // ADVICE //
    after(NaiveTextEditor editor) returning : matchAddChar(editor) || matchDelChar(editor) {
        if(root == null && current == null) {
            root = new Node(editor.getText());
            current = root;
        } else {
            Node newNode = current.addChild(editor.getText());
            current = newNode;
        }

        // printState("Add/Del");
    }

    after(NaiveTextEditor editor) returning : matchUndo(editor) {
        current = current.getParent();
        editor.setText(current.getData());
        // printState("Undo");
    }

    after(NaiveTextEditor editor, int branch) returning : matchRedo(editor, branch) {
        ArrayList<Node> currChildren = current.getChildren();
        branch -= 1;

        if(branch < 0 || branch >= currChildren.size())
            throw new IndexOutOfBoundsException();

        current = currChildren.get(branch);
        editor.setText(current.getData());
        // printState("Undo");
    }

    // HELPER METHODS //
    private void printState(String caller) {
        System.out.println(caller);
        System.out.println("current:             " + current);
        System.out.println("current.getParent(): " + current.getParent());
        System.out.println("current.getData():   " + current.getData() + "\n");
    }
}
