import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Proxy;

public class Main {
    public static void main(String args[]) {
        ITestingFields tf = new WTestingFields(7, 3.14);
        InvocationHandler stateHandler = new StateHandler(tf);

        var proxy = (ITestingFields) Proxy.newProxyInstance(
                tf.getClass().getClassLoader(),
                tf.getClass().getInterfaces(),
                stateHandler);

        proxy.setAnswer(256);
        proxy.message();
    }
}
