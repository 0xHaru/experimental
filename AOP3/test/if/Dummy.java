public class Dummy {
    private String[] strings;

    public Dummy(String[] strings) {
        this.strings = strings;
    }

    public void print() {
        for (String str : strings)
            System.out.print(str + " ");

        System.out.println();
    }

    public static void main(String[] args) {
        Dummy d1 = new Dummy(new String[] { "1", "2", "3" });
        Dummy d2 = new Dummy(new String[] { "1", "2", "3", "4" });

        d1.print();
        d2.print();
    }
}

// ajc -1.9 *.java *.aj && aj Dummy
