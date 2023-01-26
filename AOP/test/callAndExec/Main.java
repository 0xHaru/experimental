public class Main {
    public static void main(String[] args) {
        Dummy d = new Dummy();
        int res = d.dummy(10);
        System.out.println("Main::main() -> " + res);
    }
}

// ajc -1.9 Main.java Dummy.java CallExec.aj
// aj Main
// rm -f *.class
