import java.util.ArrayList;
import java.util.List;

public class Recognizer {
    List<Class<?>> classes;
    List<String> members;
    List<ClassAnalyzer> analyzers;

    public Recognizer(List<String> classes, List<String> members) throws ClassNotFoundException {
        this.classes = new ArrayList<>();
        this.members = new ArrayList<>();
        this.analyzers = new ArrayList<>();

        for (String className : classes)
            this.classes.add(Class.forName(className));

        this.members = members;

        for (Class<?> cls : this.classes)
            analyzers.add(new ClassAnalyzer(cls));

    }

    public Boolean check() {
        List<String> allMembers = new ArrayList<>();

        for (ClassAnalyzer analyzer : analyzers)
            allMembers.addAll(analyzer.getDeclaredMembers());

        for (String member : members)
            if (!allMembers.contains(member))
                return false;

        return true;
    }

    public void recognize() {
        StringBuilder builder = new StringBuilder();
        String tab = "    ";

        for (String member : members) {
            for (ClassAnalyzer analyzer : analyzers) {
                if (!analyzer.getDeclaredMembers().contains(member))
                    continue;

                builder.append("\n" + member + " ->\n");
                builder.append(tab + "Class: " + analyzer.getClassName() + "\n");
                builder.append(tab + "Type: ");

                if (analyzer.getDeclaredFields().contains(member) &&
                        analyzer.getDeclaredMethods().contains(member)) {
                    builder.append("field, method\n");
                    builder.append(tab + "Signature(s):\n");

                    for (String sig : analyzer.getFieldSignatures(member))
                        builder.append(tab + tab + sig + "\n");

                    for (String sig : analyzer.getMethodSignatures(member))
                        builder.append(tab + tab + sig + "\n");

                } else if (analyzer.getDeclaredFields().contains(member)) {
                    builder.append("field\n");
                    builder.append(tab + "Signature(s):\n");

                    for (String sig : analyzer.getFieldSignatures(member))
                        builder.append(tab + tab + sig + "\n");
                } else {
                    builder.append("method\n");
                    builder.append(tab + "Signature(s):\n");

                    for (String sig : analyzer.getMethodSignatures(member))
                        builder.append(tab + tab + sig + "\n");
                }
            }
        }

        System.out.print(builder.toString());
    }
}
