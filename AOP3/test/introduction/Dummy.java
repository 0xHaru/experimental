public class Dummy {
    public static void main(String[] args) {
        Dummy d = new Dummy();

        System.out.println(d.name);
        d.printHelloWorld();

        System.out.println(Dummy.lastName);
        Dummy.printFooBar();
    }
}

// ajc -1.9 *.java *.aj && aj Dummy
