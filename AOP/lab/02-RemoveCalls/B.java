public class B {
    A a;
    C c;

    public B() {
        a = new A();
        c = new C();
    }

    public void b(String caller) {
        a.a(caller + "B::b() -> "); // This is not allowed, let's skip it!
        c.c(caller + "B::b() -> ");
    }
}
