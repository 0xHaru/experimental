public class Main {
    public static void main(String[] args) {
        StringBuilder builder = new StringBuilder();

        System.out.println("Main.java - StringBuilder.append()");
        builder.append(new char[] {});

        System.out.println("---\nMain.java - StringBuilder.insert()");
        builder.insert(0, "");
    }
}
