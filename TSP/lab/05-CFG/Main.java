import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class Main {
    public static void main(String[] args) {
        try {
            var controlFlowGraph = new ArrayList<Edge>();
            var classes = new ArrayList<Class<?>>();
            classes.add(Painter.class);
            classes.add(Brush.class);
            classes.add(Toolbox.class);

            List<Method> methods = classes.stream()
                    .map(cls -> cls.getDeclaredMethods())
                    .flatMap(methodsArray -> Arrays.stream(methodsArray))
                    .collect(Collectors.toList());

            for (var method : methods) {
                InvokedMethods annotation = method.getAnnotation(InvokedMethods.class);

                if (annotation == null)
                    continue;

                List<String> invokedMethods = List.of(annotation.value());
                String sourceNode = method.getDeclaringClass().getName();

                for (var methodName : invokedMethods) {
                    var destNode = methodName.split("\\.")[0];
                    controlFlowGraph.add(new Edge(sourceNode, destNode, methodName));
                }
            }

            System.out.println("Edges:");
            controlFlowGraph.forEach(edge -> System.out.println("    " + edge));
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
