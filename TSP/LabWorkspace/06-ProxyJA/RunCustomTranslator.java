import javassist.ClassPool;
import javassist.Loader;

public class RunCustomTranslator {
	public static void main(String[] args) {
		try {
			CustomTranslator translator = new CustomTranslator();
			ClassPool pool = ClassPool.getDefault();
			Loader loader = new Loader(pool);
			loader.addTranslator(pool, translator);
			loader.run("Main", args);
		} catch (Throwable e) {
			e.printStackTrace();
		}
	}
}
