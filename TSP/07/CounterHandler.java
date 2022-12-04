import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;

public class CounterHandler extends NestedCalls implements InvocationHandler {
    private static final Class<?> superclass = NestedCalls.class;
    private final INestedCalls proxy;
    private int counter;

    public CounterHandler() {
        // Control flow -> 0
        System.out.println(0);
        proxy = (INestedCalls) Proxy.newProxyInstance(
                this.getClass().getClassLoader(),
                superclass.getInterfaces(),
                this);
    }

    public Object invoke(Object proxy, Method method, Object[] args) {
        try {
            // Control flow -> 2
            System.out.println(2);
            String methodName = method.getName();
            Class<?>[] paramTypes = method.getParameterTypes();
            Method superMethod = superclass.getDeclaredMethod(methodName, paramTypes);

            counter += 1;
            String depth = repeatString("-", counter);
            System.out.println(depth + " " + methodName + "()");

            // Enters a recursive loop!!
            // Object result = superMethod.invoke(this, args);

            System.out.println(3);
            // MethodHandle handle = MethodHandles.lookup().unreflectSpecial(superMethod,
            // this.getClass());
            // Object result = handle.bindTo(this).invokeWithArguments(args);
            Object result = superMethod.invoke(this, args);
            System.out.println(5);

            counter -= 1;
            return result;
        } catch (Throwable e) {
            e.printStackTrace();
            return null;
        }
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
        System.out.println(1);
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
