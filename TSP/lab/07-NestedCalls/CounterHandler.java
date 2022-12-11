import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;

public class CounterHandler extends NestedCalls implements InvocationHandler {
    private final Class<?> superclass; // NestedCalls.java
    private final Class<?> thisclass; // CounterHandler.java
    private final INestedCalls proxy;
    private int counter;

    public CounterHandler() {
        // Control flow -> 0
        superclass = super.getClass().getSuperclass();
        thisclass = this.getClass();

        proxy = (INestedCalls) Proxy.newProxyInstance(
                thisclass.getClassLoader(),
                superclass.getInterfaces(),
                this);

        counter = 0;
    }

    public Object invoke(Object proxy, Method method, Object[] args)
            throws NoSuchMethodException, IllegalAccessException, Throwable {
        // Control flow -> 2
        String methodName = method.getName();
        Class<?>[] paramTypes = method.getParameterTypes();
        Method superMethod = superclass.getDeclaredMethod(methodName, paramTypes);

        counter += 1;
        String depth = repeatString("-", counter);
        System.out.println(depth + " " + methodName + "()");

        // WRONG: Enters a recursive loop!!
        // Object result = superMethod.invoke(this, args);

        MethodHandle handle = MethodHandles.lookup()
                .unreflectSpecial(superMethod, thisclass);
        Object result = handle.bindTo(this).invokeWithArguments(args);

        counter -= 1;
        return result;
    }

    private String repeatString(String string, int times) {
        StringBuilder builder = new StringBuilder(string.length() * times);

        for (int i = 0; i < times; i += 1)
            builder.append(string);

        return builder.toString();
    }

    @Override
    public int a() {
        // Control flow -> 1
        return proxy.a();
    }

    @Override
    public int b(int a) {
        // Control flow -> 1
        return proxy.b(a);
    }

    @Override
    public int c(int a) {
        // Control flow -> 1
        return proxy.c(a);
    }
}
