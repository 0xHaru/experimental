public class Main {
    public static void main(String args[]) {
        B b = new B();
        b.b("Main::main() -> ");
    }
}

// B is not allowed to directly call A
//
// B::b() -> C::c() -> A::a() is allowed
// B::b() -> A::a() is NOT allowed
//
//
// WITHOUT ASPECTJ
//
// > javac *.java
// > java Main
//
// Output:
// A::a() was called! Control flow: Main::main() -> B::b() -> A::a()
// A::a() was called! Control flow: Main::main() -> B::b() -> C::c() -> A::a()
//
//
// WITH ASPECTJ
//
// > ajc *.aj *.java
// > aj Main
//
// Output:
// Skipping call(void A.a(String))
// A::a() was called! Control flow: Main::main() -> B::b() -> C::c() -> A::a()
