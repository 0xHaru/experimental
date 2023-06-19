public class Main {
    public static void main(String[] argv) {
        try {
            INestedCalls proxy = new CounterHandler();

            System.out.println("a() => " + proxy.a());
            System.out.println("b(a()) => " + proxy.b(proxy.a()));
            System.out.println("c(b(a())) => " + proxy.c(proxy.b(proxy.a())));
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
