import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.util.ArrayList;
import java.util.List;

public class ClassAnalyzer {
    private Class<?> cls;

    public ClassAnalyzer(Class<?> cls) {
        this.cls = cls;
    }

    public String getClassName() {
        return cls.getName();
    }

    public List<String> getDeclaredFields() {
        List<String> fields = new ArrayList<>();

        for (Field field : cls.getDeclaredFields())
            fields.add(field.getName());

        return fields;
    }

    public List<String> getDeclaredMethods() {
        List<String> methods = new ArrayList<>();

        for (Method method : cls.getDeclaredMethods())
            methods.add(method.getName());

        return methods;
    }

    public List<String> getDeclaredMembers() {
        List<String> members = new ArrayList<>(this.getDeclaredFields());
        members.addAll(this.getDeclaredMethods());
        return members;
    }

    private String getFieldSignature(Field field) {
        String modifiers = Modifier.toString(field.getModifiers());
        String type = field.getType().getName();
        String name = field.getName();

        StringBuilder builder = new StringBuilder();
        builder.append(modifiers + " ");
        builder.append(type + " ");
        builder.append(name);

        return builder.toString();
    }

    public List<String> getFieldSignatures(String fieldName) {
        List<String> fields = new ArrayList<>();

        for (Field field : cls.getDeclaredFields())
            if (field.getName().equals(fieldName))
                fields.add(getFieldSignature(field));

        return fields;
    }

    private String getMethodSignature(Method method) {
        String modifiers = Modifier.toString(method.getModifiers());

        String returnType = method.getReturnType().toString();
        int i = returnType.lastIndexOf(".");
        returnType = returnType.substring(i + 1);

        String name = method.getName();
        List<String> paramTypes = new ArrayList<>();

        for (Class<?> cls : method.getParameterTypes()) {
            String className = cls.getName();
            int j = className.lastIndexOf(".");
            className = className.substring(j + 1);
            paramTypes.add(className);
        }

        List<String> paramNames = new ArrayList<>();

        for (Parameter param : method.getParameters())
            paramNames.add(param.getName());

        StringBuilder builder = new StringBuilder();
        builder.append(modifiers + " ");
        builder.append(returnType + " ");
        builder.append(name + "(");

        for (int j = 0; j < paramTypes.size(); j += 1) {
            builder.append(paramTypes.get(j) + " ");
            builder.append(paramNames.get(j));

            if (j < paramTypes.size() - 1)
                builder.append(", ");
        }

        builder.append(")");

        List<String> exceptionTypes = new ArrayList<>();

        for (Class<?> cls : method.getExceptionTypes()) {
            String className = cls.getName();
            int j = className.lastIndexOf(".");
            className = className.substring(j + 1);
            exceptionTypes.add(className);
        }

        if (exceptionTypes.size() > 0) {
            builder.append(" throws ");

            for (int j = 0; j < exceptionTypes.size(); j += 1) {
                builder.append(exceptionTypes.get(j));

                if (j < exceptionTypes.size() - 1)
                    builder.append(", ");
            }
        }

        return builder.toString();
    }

    public List<String> getMethodSignatures(String methodName) {
        List<String> methods = new ArrayList<>();

        for (Method method : cls.getDeclaredMethods())
            if (method.getName().equals(methodName))
                methods.add(getMethodSignature(method));

        return methods;
    }
}
