import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

public class DumpMethods {
    private static List<Method> getPublicMethods(Class<?> cls) {
        List<Method> publicMethods = new ArrayList<>();

        // getDeclaredMethods() only includes methods in the class (good)
        // but also includes protected and private methods (bad)
        Method[] declaredMethods = cls.getDeclaredMethods();

        for (Method method : declaredMethods) {
            // Only public methods allowed
            if (!Modifier.isPublic(method.getModifiers()))
                continue;

            // Only instance methods allowed
            if (Modifier.isStatic(method.getModifiers()))
                continue;

            publicMethods.add(method);
        }

        return publicMethods;
    }

    public static void main(String args[]) {
        try {
            String className = args[0];
            Class<?> cls = Class.forName(className);
            List<Method> methods = getPublicMethods(cls);

            System.out.println("Public instance methods of \"" + className + "\":");

            for (Method method : methods)
                System.out.println("    " + method.toString());
        } catch (ClassNotFoundException e) {
            System.err.println(e);
        }
    }
}
