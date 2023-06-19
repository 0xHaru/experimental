import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.regex.Pattern;

public class InvokeUnknownMethod {
    public static void main(String args[]) {
        try {
            String className = args[0];
            String methodName = args[1];
            String params[] = Arrays.copyOfRange(args, 2, args.length);

            Class<?> paramsTypes[] = new Class[params.length];
            Object invokeArgs[] = new Object[params.length];

            String pattern = "-?[0-9]+.[0-9]+";

            for (int i = 0; i < params.length; i += 1) {
                if (Pattern.matches(pattern, params[i])) {
                    paramsTypes[i] = Double.TYPE;
                    invokeArgs[i] = Double.parseDouble(params[i]);
                } else {
                    paramsTypes[i] = Integer.TYPE;
                    invokeArgs[i] = Integer.parseInt(params[i]);
                }
            }

            Class<?> cls = Class.forName(className);
            Method method = cls.getMethod(methodName, paramsTypes);
            Constructor<?> cons = cls.getDeclaredConstructor();

            Object result = method.invoke(cons.newInstance(), invokeArgs);
            System.out.println(result.toString());
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}

// Caught exceptions:
//
// ClassNotFoundException
// NoSuchMethodException
// IllegalAccessException
// InvocationTargetException
// InstantiationException
// IllegalAccessException
// InvocationTargetException
