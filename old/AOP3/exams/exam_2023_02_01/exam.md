# Exercise on AOSD: Tree Undo/Redo.

Any text editor allows to undo and redo the latest editings.

Unfortunately, most of the available undo/redo operations implement a linear browsing of the changelog.

Therefore, if you undo an editing and then you add some new text a successive redo operations will merely fail and any combination of undo/redo wouldn't permit to restore the deleted text.

To enable the restoring of the lost text, we need to browse (and so to store) the changelog as a tree.

Let's consider the following naive implementation of an editor:

```java
import java.util.Vector;

public class NaiveTextEditor {
    private Vector<Character> text;

    public NaiveTextEditor() { text = new Vector<Character>(10, 10); }

    public void addChar(char ch) { text.addElement (ch); }

    public char delChar() {
        Character ch = text.elementAt(text.size() - 1);
        text.removeElementAt(text.size() - 1);
        return ch;
    }

    public String toString() { return text.toString(); }
}
```

The goal of the exercise is to write an aspect UndoRedoAspect that enhances such an editor with the tree-based undo/redo operations with the following interface:

```java
public interface UndoRedoInterface {
    public void undo();
    public void redo (int brach);
}
```

Both `undo()` and `redo()` move along the tree of one step at each call; the argument for the `redo()` method specifies which branch of the tree to follow; branches are chronologically sorted (the oldest will be the leftmost).

As an example, let's see this main and the corresponding expected result.

```java
public class EditorMain {
    public static void main(String[] args) {
        NaiveTextEditor nte = new NaiveTextEditor();
        for (char i = 'a'; i < 'l'; i++) nte.addChar(i);
        System.out.println(nte);
        nte.undo();
        nte.undo();
        System.out.println("### " + nte);
        for (int i = 0; i <= 2; i++) nte.delChar();
        System.out.println(nte);
        nte.undo();
        System.out.println("### " + nte);
        nte.redo(1);
        System.out.println("### " + nte);
        for (int i = 0; i < 3; i++) nte.undo();
        System.out.println("### " + nte);
        nte.redo(2);
        System.out.println("### " +nte);
    }
}
```

```text
[23:47] cazzola@ulik:~/tsp>java NaiveTextEditor
[a, b, c, d, e, f, g, h, i, j, k]
### [a, b, c, d, e, f, g, h, i]
[a, b, c, d, e, f]
### [a, b, c, d, e, f, g]
### [a, b, c, d, e, f]
### [a, b, c, d, e, f, g, h, i]
### [a, b, c, d, e, f, g, h, i, j]
[23:47] cazzola@ulik:~/tsp>
```

Note the output of your code should be compliant with the one above.

If you think it is necessary, implement all the modules, packages, classes, interfaces and methods but please consider that this will contribute to the final mark and one of the requirements is to forge a good quality solution.

If you would like to change the given source code you can only do that by using Javassist, BCEL or Aspect]; any other way (e.g., by using an editor) will be considered wrong.
