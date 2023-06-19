import javassist.ClassPool;
import javassist.Loader;

public class RunTranslator {
    public static void main(String[] args) {
        try {
            HelloWorldTranslator translator = new HelloWorldTranslator();
            ClassPool pool = ClassPool.getDefault();
            Loader loader = new Loader(pool);
            loader.addTranslator(pool, translator);
            loader.run("Main", args); // Loads a class and calls main() in that class
        } catch (Throwable e) {
            e.printStackTrace();
        }
    }
}

// javac -cp .:../javassist/javassist.jar *.java
// java -cp .:../javassist/javassist.jar RunTranslator
