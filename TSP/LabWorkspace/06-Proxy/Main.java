import java.lang.reflect.Proxy;

public class Main {
	public static void main(String[] args) {
		ITestingFields tf = new WTestingFields(10, 1.0);
		StateHandler handler = new StateHandler(tf);
		
		ITestingFields proxy = (ITestingFields) Proxy.newProxyInstance(
				tf.getClass().getClassLoader(), 
				tf.getClass().getInterfaces(), 
				handler);
		
		proxy.setAnswer(1);
		System.out.println();
		proxy.message();
	}
}
