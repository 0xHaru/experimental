public class Main {
    public static void main(String[] args) {
        DummyA da = new DummyA();
        DummyB db = new DummyB();

        System.out.println("Main.java - " + da.a()); // 4
        System.out.println("Main.java - " + db.a()); // 3
    }
}

// ajc -1.9 *.java *.aj && aj Main
