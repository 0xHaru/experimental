import java.lang.reflect.Field;
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class StateHandler implements InvocationHandler {
	private Object target;

	public StateHandler(Object target) {
		this.target = target;
	}

	@Override
	public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {
		System.out.println("Before invoking " + method.getName());
		printTargetState();

		Object result = method.invoke(target, args);

		System.out.println("After invoking " + method.getName());
		printTargetState();

		return result;
	}

	private void printTargetState() throws IllegalAccessException {
		Field[] classFields = target.getClass().getDeclaredFields();
		Field[] superclassFields = target.getClass().getSuperclass().getDeclaredFields();
		List<Field> fields = new ArrayList<>(Arrays.asList(classFields));
		fields.addAll(Arrays.asList(superclassFields));

		for (Field field : fields) {
			field.trySetAccessible();
			Object fieldValue = field.get(target);
			System.out.print(field.getName() + " = ");

			if (!field.getType().isArray()) {
				System.out.println(fieldValue);
				continue;
			}

			for (Double n : (Double[]) fieldValue)
				System.out.print(n + " ");

			System.out.println();
		}
	}
}
