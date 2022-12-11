public class DummyStack {
    private boolean empty;
    private int size;

    private Object secretStackMethod(DummyStack stack, DummyQueue queue)
            throws IllegalArgumentException, NullPointerException {
        return null;
    }

    public boolean empty() {
        return empty;
    }

    public int peek() {
        return 0;
    }

    public void push(int item) {
    }

    public int pop() {
        return 0;
    }

    public int size() {
        return size;
    }
}
