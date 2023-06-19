public class Dummy {
    private static int data;
    public String name;

    public Dummy() {
        this.name = "dummy";
    }

    static public int init() {
        return 42;
    }

    public void accessToNull() {
        try {
            Dummy dummy = null;
            System.out.println(dummy.toString());
        } catch (NullPointerException e) {
            e.printStackTrace();
        }
    }

    public String toString() {
        return "name: " + this.name + " - data: " + Dummy.data;
    }

    static {
        data = init();
    }
}
