import java.io.FileInputStream;
import java.io.IOException;

public class CounterClassLoader extends ClassLoader {
    private int javaClasses;
    private int userClasses;

    public CounterClassLoader(ClassLoader parent) {
        super(parent);
        javaClasses = 0;
        userClasses = 0;
    }

    @Override
    public Class<?> loadClass(String className) throws ClassNotFoundException {
        if (className.startsWith("java.")) {
            javaClasses += 1;
            logCurrentState(className, true);
            return super.loadClass(className);
        } else {
            userClasses += 1;
            logCurrentState(className, false);
            return findClass(className);
        }
    }

    private void logCurrentState(String className, boolean isJavaClass) {
        String type = isJavaClass ? "JAVA" : "USER";
        System.out.println("Loading " + type + " class: " + className);
        System.out.print("Java classes: " + javaClasses);
        System.out.println(" | User classes: " + userClasses);
        System.out.println("---");
    }

    @Override
    public Class<?> findClass(String className) throws ClassNotFoundException {
        try {
            String filename = className.replace(".", "/") + ".class";
            FileInputStream fileInputStream;

            fileInputStream = new FileInputStream(filename);
            byte[] bytecode = fileInputStream.readAllBytes();
            fileInputStream.close();

            if (bytecode != null)
                return defineClass(className, bytecode, 0, bytecode.length);

            throw new IOException();
        } catch (IOException e) {
            throw new ClassNotFoundException();
        }
    }

    @Override
    public String getName() {
        return this.getClass().getName();
    }
}
