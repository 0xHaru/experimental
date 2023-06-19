public class C {
    A a;

    public C() {
        a = new A();
    }

    public void c(String caller) {
        a.a(caller + "C::c() -> ");
    }
}
