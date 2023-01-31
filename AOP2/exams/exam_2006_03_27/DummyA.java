public class DummyA {
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
        return e();
    }

    public String e() {
        return "DummyA";
    }
}
