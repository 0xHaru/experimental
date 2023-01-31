public class DummyB {
    public String a() {
        return b();
    }

    public String b() {
        return c();
    }

    public String c() {
        return d();
    }

    public String d() {
        return "DummyB";
    }
}
