import javassist.ClassPool;
import javassist.CtClass;
import javassist.CtField;
import javassist.CtMethod;

public class StringBuilderGenerator {
    public static void main(String[] args) throws Exception {
        ClassPool pool = ClassPool.getDefault();
        CtClass builder = pool.getCtClass("java.lang.StringBuilder");

        builder.addField(new CtField(CtClass.longType, "start", builder));

        CtMethod append = builder.getDeclaredMethod("append",
                new CtClass[] { pool.getCtClass("char[]") });

        CtMethod insert = builder.getDeclaredMethod("insert",
                new CtClass[] { CtClass.intType, pool.getCtClass("java.lang.String") });

        String before = "start = System.currentTimeMillis();";

        String after = "long end = System.currentTimeMillis();"
                + "System.out.println(\"Start: \" + Long.toString(start));"
                + "System.out.println(\"End: \" + Long.toString(end));"
                + "System.out.println(\"Elapsed: \" + Long.toString(end - start));";

        append.insertBefore(before);
        append.insertAfter(after);

        insert.insertBefore(before);
        insert.insertAfter(after);

        builder.writeFile();
    }
}
