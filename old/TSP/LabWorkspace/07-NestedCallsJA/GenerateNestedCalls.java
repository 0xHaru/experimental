import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.Method;
import java.lang.reflect.Proxy;

import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtField;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.CtNewMethod;

public class GenerateNestedCalls {
	public static void main(String[] args) {
		try {
			ClassPool pool = ClassPool.getDefault();
			pool.importPackage("java.lang.invoke.MethodHandle");
			pool.importPackage("java.lang.invoke.MethodHandles");
			pool.importPackage("java.lang.reflect.InvocationHandler");
			pool.importPackage("java.lang.reflect.Method");
			pool.importPackage("java.lang.reflect.Proxy");
			
			// Create CounterHandler.class
			CtClass nestedCalls = pool.get("NestedCalls");
			CtClass counterHandler = pool.makeClass("CounterHandler", nestedCalls);
			
			CtClass invocationHandler = pool.get("java.lang.reflect.InvocationHandler");
			counterHandler.addInterface(invocationHandler);
			
			counterHandler.addField(CtField.make("private final Class superclass;", counterHandler));
			counterHandler.addField(CtField.make("private final Class thisclass;", counterHandler));
			counterHandler.addField(CtField.make("private final INestedCalls proxy;", counterHandler));
			counterHandler.addField(CtField.make("private int counter;", counterHandler));
			
			CtConstructor cons = CtNewConstructor
					.make(" public CounterHandler() {"
							+ "		superclass = super.getClass().getSuperclass();"
							+ "		thisclass = this.getClass();"
							+ "		proxy = (INestedCalls) Proxy.newProxyInstance("
							+ "				thisclass.getClassLoader(),"
							+ "				superclass.getInterfaces(),"
							+ "				this);"
							+ "		counter = 0;"
							+ "	}", counterHandler);
			counterHandler.addConstructor(cons);
			
			CtMethod repeatString = CtNewMethod
					.make("	private String repeatString(String string, int times) {"
							+ "		StringBuilder builder = new StringBuilder(string.length() * times);"
							+ "		for(int i = 0; i < times ; i += 1)"
							+ "			builder.append(string);"
							+ "		return builder.toString();"
							+ "	}", counterHandler);
			counterHandler.addMethod(repeatString);
			
			CtMethod invoke = CtNewMethod
					.make("	public Object invoke(Object proxy, Method method, Object[] args) throws Throwable {"
							+ "		String methodName = method.getName();"
							+ "		Class[] paramTypes = method.getParameterTypes();"
							+ "		Method superMethod = superclass.getDeclaredMethod(methodName, paramTypes);"
							+ "		counter += 1;"
							+ "		String depth = repeatString(\"-\", counter);"
							+ "		System.out.println(depth + \" \" + methodName + \"()\");"
							+ "		MethodHandle handle = MethodHandles.lookup().unreflectSpecial(superMethod, thisclass);"
							+ "		Object result = handle.bindTo(this).invokeWithArguments(args);"
							+ "		counter -= 1;"
							+ "		return result;"
							+ "	}", counterHandler);
			counterHandler.addMethod(invoke);
			
			CtMethod a = CtNewMethod.make("public int a() { return proxy.a(); }", counterHandler);
			counterHandler.addMethod(a);
			
			CtMethod b = CtNewMethod.make("public int b(int a) { return proxy.b(a); }", counterHandler);
			counterHandler.addMethod(b);
			
			CtMethod c = CtNewMethod.make("public int c(int a) { return proxy.c(a); }", counterHandler);
			counterHandler.addMethod(c);
			
			counterHandler.writeFile();
			
			// Create Main.class
			CtClass main = pool.makeClass("Main");
			
			CtMethod mainMethod = CtNewMethod
					.make("	public static void main(String[] args) {"
							+ "		try {"
							+ "			INestedCalls proxy = new CounterHandler();"
							+ "			System.out.println(\"a() => \" + proxy.a());"
							+ "			System.out.println(\"b(a()) => \" + proxy.b(proxy.a()));"
							+ "         System.out.println(\"c(b(a())) => \" + proxy.c(proxy.b(proxy.a())));"
							+ "		} catch (Exception e) {"
							+ "			System.err.println(e);"
							+ "		}"
							+ "	}", main);
			main.addMethod(mainMethod);
			
			main.writeFile();
		} catch(Exception e) {
//			System.err.println(e);
			e.printStackTrace();
		}
	}
}
