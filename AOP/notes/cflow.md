# What is clow?

cflow helps you to advice the whole control flow. Let's try an example, I have 4 small classes:

```java
public class A {

    public static void methodA() {
        B.methodB();
    }

}

public class B {

    public static void methodB() {
        C.methodC();
        int a = 1;
        int b = 2;
        System.out.println( a + b );
    }

}

public class C {

    public static void methodC() {
        D.methodD();
    }

}

public class D {

    public static void methodD() {

    }

}
```

my aspect:

```
public aspect CFlow {

    public pointcut flow() : cflow(call( * B.methodB() ) ) && !within(CFlow);

    before() : flow() {
        System.out.println( thisJoinPoint );
    }

}
```

and my runner (just to see what happens):

```java
public class Test {

    public static void main(String[] args) {
        A.methodA();
    }
}
```

in my pointcut you could see `cflow(call( * B.methodB()))`, so I want to aspect control flow starting from B.methodB calling, and when you run `Test` class you see on console:

```
call(void test.B.methodB())
staticinitialization(test.B.<clinit>)
execution(void test.B.methodB())
call(void test.C.methodC())
staticinitialization(test.C.<clinit>)
execution(void test.C.methodC())
call(void test.D.methodD())
staticinitialization(test.D.<clinit>)
execution(void test.D.methodD())
get(PrintStream java.lang.System.out)
call(void java.io.PrintStream.println(int))
3
```

last string does not belong to aspect, it is just because of `System.out.println` inside `methodB`.

All printed shows you control flow - chains of methods and 'events' (execution, calling, initializations...). You see, I started from `Test` class, which called `methodA` but they are not in 'stack', because we were interested in `methodB` control flow.

If you want to get that stack, but without first line (calling itself), you could try to define:

```
public pointcut flow() :  cflowbelow(call( * B.methodB() ) ) && !within(CFlow);
```

`cflowbelow` is another pointcut, which means control flow excluding specified (in our case calling `B.methodB`).

Be careful to add `!within(_aspect_)` in pointcut, otherwise you will get nothing good but `StackOverflowError`. It happens because cflow can't be defined at compile time, and at runtime aspect belongs to control flow too (so it leads to eternal recursion...).

Well, think of control flow as similar to call stack, then you will get an idea of its usage.

Source: https://stackoverflow.com/questions/5205916/aspect-oriented-programming-what-is-cflow
