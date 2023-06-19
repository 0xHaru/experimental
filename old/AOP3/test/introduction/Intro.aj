public aspect Intro {
    public String Dummy.name = "Mr. Dummy";

    public void Dummy.printHelloWorld() {
        System.out.println("Hello world!");
    }

    public static String Dummy.lastName = "DumDum";

    public static void Dummy.printFooBar() {
        System.out.println("FooBar");
    }
}
