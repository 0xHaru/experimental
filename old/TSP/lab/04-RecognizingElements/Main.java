import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Main {
    private static List<String> getMembersHelper(String className) throws ClassNotFoundException {
        Class<?> cls = Class.forName(className);

        List<String> members = new ArrayList<>();
        Field[] fields = cls.getDeclaredFields();
        Method[] methods = cls.getDeclaredMethods();

        for (Field field : fields)
            members.add(field.getName());

        for (Method method : methods)
            members.add(method.getName());

        return members;
    }

    private static List<String> getMembers(List<String> classes) throws ClassNotFoundException {
        List<String> members = new ArrayList<>();

        for (String cls : classes)
            members.addAll(Main.getMembersHelper(cls));

        Set<String> set = new HashSet<>(members);
        members.clear();
        members.addAll(set);

        return members;
    }

    public static void main(String args[]) {
        try {
            List<String> classes = Arrays.asList("DummyStack", "DummyQueue");
            List<String> members = getMembers(classes);
            System.out.println("Members: " + members);
            Recognizer recognizer = new Recognizer(classes, members);

            if (recognizer.check())
                System.out.println("All the members are present in at least of the input classes");
            else
                System.out.println("One or more of the members are NOT present in any of the input classes");

            recognizer.recognize();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
