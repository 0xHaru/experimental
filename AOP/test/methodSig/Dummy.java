public class Dummy {
    public void dummy(int x) {
        System.out.println(x);
    }

    public static void main(String[] args) {
        Dummy d = new Dummy();
        d.dummy(10);
    }
}

// ajc -1.9 Dummy.java MethodSig.aj
// aj Dummy
// rm -f *.class
