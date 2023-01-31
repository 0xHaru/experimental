public class Main {
    public static void main(String args[]) {
        Dummy dummy = new Dummy();

        // Dummy.succ(1) will be applied twice so the expected output is gonna be 3
        System.out.println("Main::main - succ(1) = " + dummy.succ(1));

        System.out.println("Main::main - sum(5, 5) = " + dummy.sum(5, 5));
    }
}
