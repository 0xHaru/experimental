import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.lang.instrument.ClassFileTransformer;
import java.security.ProtectionDomain;

import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtMethod;

public class HelloWorldTransformer implements ClassFileTransformer {
    @Override
    public byte[] transform(ClassLoader loader,
            String className,
            Class<?> classBeingRedefined,
            ProtectionDomain protectionDomain,
            byte[] classfileBuffer) {
        if (className.equals("Main")) {
            try {
                ClassPool pool = ClassPool.getDefault();
                InputStream bytes = new ByteArrayInputStream(classfileBuffer);
                CtClass main = pool.makeClass(bytes);
                CtMethod mainMethod = main.getDeclaredMethod("main");
                mainMethod.insertBefore("System.out.println(\"Hello World!\");");
                return main.toBytecode();
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        return classfileBuffer;
    }
}

// ALTERNATIVE:
// ...
// ClassPool pool = ClassPool.getDefault();
// CtClass main = pool.get("Main");
// CtMethod mainMethod = main.getDeclaredMethod("main");
// mainMethod.insertBefore("System.out.println(\"Hello World!\");");
// return main.toBytecode();
// ...
