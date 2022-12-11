import java.io.IOException;

import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtConstructor;
import javassist.CtField;
import javassist.CtMethod;
import javassist.CtNewConstructor;
import javassist.NotFoundException;
import javassist.Translator;

public class CustomTranslator implements Translator {
	@Override
	public void start(ClassPool pool) throws NotFoundException, CannotCompileException {
		try {
			// Create ITestingFiels (interface)
			CtClass iTestingFields = pool.makeInterface("ITestingFields");
			CtMethod setAnswer = CtMethod.make("public void setAnswer(int a);", iTestingFields);
			CtMethod message = CtMethod.make("public String message();", iTestingFields);
			iTestingFields.addMethod(setAnswer);
			iTestingFields.addMethod(message);
			iTestingFields.writeFile();

			// Create TraceHandler (class)
			pool.importPackage("java.lang.reflect.Method");
			pool.importPackage("java.lang.reflect.Proxy");
			
			CtClass traceHandler = pool.makeClass("TraceHandler");
			traceHandler.addInterface(pool.get("java.lang.reflect.InvocationHandler"));

			CtField target = CtField.make("private Object target;", traceHandler);
			traceHandler.addField(target);

			CtConstructor cons = CtNewConstructor
					.make("public TraceHandler(Object target) { this.target = target; }",
					traceHandler);
			traceHandler.addConstructor(cons);
	
			CtMethod invoke = CtMethod
					.make("public Object invoke(Object proxy, Method m, Object[] args)"
				    + "throws Throwable {"
					+ "System.out.println(\"Before \" + m.getName());"
					+ "Object result = m.invoke(target, args);"
					+ "System.out.println(\"After \" + m.getName());"
					+ "return result;"
					+ "}", traceHandler);
			traceHandler.addMethod(invoke);
		
			traceHandler.writeFile();
			
			// Create Main (class)
			CtClass main = pool.makeClass("Main");
			
			CtMethod mainMethod = CtMethod
					.make("public static void main(String[] args) {"
					+ "TestingFields tf = new TestingFields(10, 0.0);"
					+ "ITestingFields proxy = (ITestingFields) Proxy.newProxyInstance("
					+ "tf.getClass().getClassLoader(),"
					+ "tf.getClass().getInterfaces(),"
					+ "new TraceHandler(tf));"
					+ "proxy.message();"
					+ "}", main);
			main.addMethod(mainMethod);
			main.writeFile();			
		} catch (NotFoundException | IOException | CannotCompileException e) {
			e.printStackTrace();
		}
	}

	@Override
	public void onLoad(ClassPool pool, String className) throws NotFoundException, CannotCompileException {
		try {
			if(className.equals("TestingFields")) {
				CtClass testingFields = pool.get(className);
				testingFields.addInterface(pool.get("ITestingFields"));
				testingFields.writeFile();
			}
		} catch (NotFoundException | IOException | CannotCompileException e) {
				e.printStackTrace();
		}
	}
}
