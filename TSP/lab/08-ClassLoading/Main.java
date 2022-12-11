import Foo.Bar;

public class Main {
    public static void main(String[] args) {
        try {
            var dummy = new Dummy();
            String dummyClassLoader = dummy.getClass().getClassLoader().getName();
            System.out.println("Main.java -> Dummy class loader: " + dummyClassLoader);
            System.out.println("Main.java -> dummy.getValue(): " + dummy.getValue());

            System.out.println("~~~");

            var bar = new Bar();
            String barClassLoader = bar.getClass().getClassLoader().getName();
            System.out.println("Main.java -> Bar class loader: " + barClassLoader);
            System.out.println("Main.java -> bar.getValue(): " + bar.getValue());
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
