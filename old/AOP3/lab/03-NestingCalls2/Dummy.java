public class Dummy {
    public Dummy() {
    }

    public int sum(int a, int b) {
        return a + b;
    }

    // Applied twice
    public int succ(int n) {
        System.out.println("Dummy::succ - mulByTen(1) = " + mulByTen(1));
        return n + 1;
    }

    // Applied twice
    private int mulByTen(int n) {
        return n * 10;
    }
}
