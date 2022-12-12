import javassist.CannotCompileException;
import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtMethod;
import javassist.NotFoundException;
import javassist.Translator;

public class HelloWorldTranslator implements Translator {
    @Override
    public void start(ClassPool pool) throws NotFoundException, CannotCompileException {
    }

    @Override
    public void onLoad(ClassPool pool, String classname) throws NotFoundException, CannotCompileException {
        if (classname.equals("Main")) {
            CtClass main = pool.get(classname);
            CtMethod mainMethod = main.getDeclaredMethod("main");
            mainMethod.insertBefore("System.out.println(\"Hello World!\");");
        }
    }
}
