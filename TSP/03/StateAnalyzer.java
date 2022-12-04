import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Map;

public class StateAnalyzer {
    private Object object;
    private Map<String, Field> fields;

    public StateAnalyzer(Object object) {
        this.object = object;
        this.fields = new HashMap<>();

        Field[] fields = object.getClass().getDeclaredFields();

        for (Field field : fields)
            this.fields.put(field.getName(), field);
    }

    public void setField(String fieldName, Object value) throws IllegalAccessException {
        Field field = fields.get(fieldName);
        field.setAccessible(true);
        field.set(object, value);
    }

    public static void main(String args[]) {
        try {
            TestingFields tf = new TestingFields(7, 3.14);

            System.out.println("Before:\n  " + tf.getModified() + "\n  " + tf.getS());

            StateAnalyzer analyzer = new StateAnalyzer(tf);
            analyzer.setField("modified", true);
            analyzer.setField("s", "testing ... passed!!!");

            System.out.println("After:\n  " + tf.getModified() + "\n  " + tf.getS());
        } catch (Exception e) {
            System.err.println(e);
        }
    }
}
