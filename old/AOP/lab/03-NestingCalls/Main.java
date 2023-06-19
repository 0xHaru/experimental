public class Main {
    public static void main(String args[]) {
        Dummy dummy = new Dummy();

        // Dummy.succ(1) will be applied twice so the expected output is gonna be 3
        System.out.println(dummy.succ(1));

        System.out.println(dummy.sum(5, 5));
    }
}
