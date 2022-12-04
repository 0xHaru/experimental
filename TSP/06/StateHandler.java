import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class StateHandler implements InvocationHandler {
    private Object obj;

    public StateHandler(Object obj) {
        this.obj = obj;
    }

    public Object invoke(Object proxy, Method method, Object[] args) {
        try {
            System.out.println("Before calling " + method.getName() + "():\n" + getObjectState());
            Object result = method.invoke(obj, args);
            System.out.println("After calling " + method.getName() + "():\n" + getObjectState());
            return result;
        } catch (Exception e) {
            e.printStackTrace();
            return null;
        }
    }

    private String getObjectState() throws IllegalAccessException {
        var builder = new StringBuilder();
        Field[] fields = getObjectFields();

        for (var field : fields) {
            field.trySetAccessible();
            builder.append("    " + fieldToString(field) + "\n");
        }

        return builder.toString();
    }

    private Field[] getObjectFields() {
        Field[] classFields = obj.getClass().getDeclaredFields();
        Field[] superclassFields = obj.getClass().getSuperclass().getDeclaredFields();

        return Stream.of(classFields, superclassFields)
                .flatMap(Stream::of)
                .toArray(Field[]::new);
    }

    private String arrayToString(Object array) {
        return IntStream.range(0, Array.getLength(array))
                .boxed()
                .map(i -> Array.get(array, i).toString())
                .collect(Collectors.joining(", ", "[", "]"));
    }

    private String fieldToString(Field field) throws IllegalAccessException {
        var builder = new StringBuilder();
        Object fieldValue = field.get(obj);

        builder.append(field.toString() + " = ");

        if (field.getType().isArray())
            builder.append(arrayToString(fieldValue));
        else
            builder.append(fieldValue.toString());

        return builder.toString();
    }
}
