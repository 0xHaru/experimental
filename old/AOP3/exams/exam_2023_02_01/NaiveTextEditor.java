import java.util.Vector;

public class NaiveTextEditor {
    private Vector<Character> text;

    public NaiveTextEditor() {
        text = new Vector<Character>(10, 10);
    }

    public void addChar(char ch) {
        text.addElement(ch);
    }

    public char delChar() {
        Character ch = text.elementAt(text.size() - 1);
        text.removeElementAt(text.size() - 1);
        return ch;
    }

    public String toString() {
        return text.toString();
    }
}
