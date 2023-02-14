public class Main {
    public static void main(String[] args) {
        Dummy d1 = new Dummy(100);
        Dummy d2 = new Dummy(1000);

        d1.print();
        d2.print();

        // Two different instances of the Pertarget aspect have been created
        System.out.println(Pertarget.aspectOf(d1));
        System.out.println(Pertarget.aspectOf(d2));
    }
}

// ajc -1.9 *.java *.aj && aj Main
// rm -f *.class
