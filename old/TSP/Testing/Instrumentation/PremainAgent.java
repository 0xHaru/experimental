import java.lang.instrument.Instrumentation;

public class PremainAgent {
    public static void premain(String agentArgs, Instrumentation instrumentation) {
        instrumentation.addTransformer(new HelloWorldTransformer());
    }
}
