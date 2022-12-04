public class NestedCalls implements INestedCalls {
    private int i = 0;

    public int a() {
        // return b(i++);
        System.out.println(4);
        return 1;
    }

    public int b(int a) {
        return (i < 42) ? c(b(a())) : 1;
    }

    public int c(int a) {
        return --a;
    }
}
