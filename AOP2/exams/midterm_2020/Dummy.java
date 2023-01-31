public class Dummy {
    public void m1(String s) {
        System.out.println("m1: " + s);
    }

    public void m2(int i) {
        System.out.println("m2: " + i);
    }

    public void m2(int i, String s) {
        System.out.println("m2: " + i + " && " + s);
    }

    public static void main(String[] args) {
        Dummy d1 = new Dummy();
        Dummy d2 = new Dummy();

        d1.m1("A");

        d2.m1("B");
        d2.m1("C");

        d1.m2(7);

        d2.m2(7, "D");

        d1.m2(3);

        d2.m2(3, "E");
    }
}
