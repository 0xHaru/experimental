# Riassunto

## Agent + Premain

Viene eseguito prima del caricamento delle classi e dell'esecuzione del Main vero e proprio.

**Pro:** Permette di eseguire qualsiasi modifica alle classi prima che vengano caricate.

**Contro:** Bisogna crearsi il MANIFEST.MF e compilare il tutto all'interno di un jar che andrà specificato come javaAgent nel memento di esecuzione

## Translator

Permette di modificare una classe mentre sta venendo caricata nella JVM.

Qui può essere apportata qualsiasi modifica alla classe che verrà dunque resa subito effettiva, esso deve essere applicato prima del caricamento della classe.

**Pro:** E' possibile da qui modificare la struttura delle classi in maniera selettiva, volendo anche quindi modificando la loro intera implementazione o aggiungendoci interfacce ecc...

**Contro:** Viene invocato su tutte le classi del ClassPool su cui è stato impostato.

## Proxy

Permette di aggiungere degli statment prima e/o post invocazione di una funzione. Esso verrà intercettato da tutte le chiamate.

**Pro:** Non richiede l'utilizzo di Javassist

**Contro:** E' possibile solamente aggiungere dei comportamenti pre o post invocazione, senza però poter alterare gli stessi. Al più si può negare l'invocazione.

# Modifica di Bytecode a Load Time

## Instrumentation - Agent + Premain

Il `premain` è una funzione statica che viene eseguita prima del `main` del nostro programma. In particolare viene eseguita prima del caricamento delle classi che abbiamo implementato e consente di sfrutturare le capacità di strumentazione di Java.

La strumentazione è definita come l'aggiunta di bytecode ad un metodo con lo scopo di raccogliere dei dati da utilizzare con degli strumenti come ad esempio profilers, coverage analyzers o event loggers.

Poiché le modifiche sono puramente additive, questi strumenti non modificano lo stato o il comportamento dell'applicazione.

Come prima cosa è necessario scrivere una classe che implementa l'interfaccia `ClassFileTrasformer` e fare l'override del metodo `transform`. In questo metodo vengono eseguite le modifiche al bytecode delle nostre classi tramite l'utilizzo di Javassist, una libreria per la manipolazione del bytecode.

In questo esempio, con l'aiuto di JavaAssist, inseriamo nel metodo `main` della classe `Main` un `System.out.println("Hello world!");`.

```java
import javassist.*;

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
```

Nel `premain` invochiamo il metodo `addTransformer` sull'oggetto `instrumentation` passandogli il nostro transformer `HelloWorldTransformer`.

```java
import java.lang.instrument.Instrumentation;

public class PremainAgent {
    public static void premain(String agentArgs, Instrumentation instrumentation) {
        instrumentation.addTransformer(new HelloWorldTransformer());
    }
}
```

Per poter utilizzare il premain bisogna per prima cosa creare un **agente** come file `.jar` contenente un `MANIFEST.MF` con specificato l'attributo `Premain-Class`.

1. Compilazione di tutti i file `.java`: `javac -cp .:<path-to-JA> *.java`
2. Creazione del `.jar`: `jar -m MANIFEST.MF -f Agent.jar -c PremainAgent.class`
3. Esecuzione del `Main` con l'agente: `java -cp .:<path-to-JA> -javaagent:PremainAgent.jar Main`

```
Manifest-Version: 1.0
Premain-Class: PremainAgent
```

```java
public class Main {
    public static void main(String[] args) {
        System.out.println("I'm the Main.main() method!");
    }
}
```

#### Output:

```
Hello World!
I'm the Main.main() method!
```

## Javassist - Loader + Translator

Javassist fornisce un suo class loader chiamato `Loader`, se si vuole modificare il bytecode di una classe a load time è possibile aggiungere un event listener al `Loader`. L'event listener verrà notificato quando il class loader carica una classe.

L'event listener deve implementare l'interfaccia `Translator`:

```java
public interface Translator {
    public void start(ClassPool pool);
    public void onLoad(ClassPool pool, String classname);
}
```

Il metodo `start()` viene chiamato quando il nostro `Translator` viene aggiunto ad un oggetto `Loader` tramite `addTranslator()`, mentre il metodo `onLoad()` viene chiamato appena prima che `Loader` carichi una classe e viene utilizzato per modificare il bytecode della classe che sta venendo caricata.

Risolviamo l'esempio precente utilizzando `Loader` e `Translator`.

```java
import javassist.*;

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
```

```java
import javassist.*;

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
```

```java
public class Main {
    public static void main(String[] args) {
        System.out.println("I'm the Main.main() method!");
    }
}
```

1. Compilazione di tutti i file `.java`: `javac -cp .:<path-to-JA> *.java`
2. Esecuzione di `RunTranslator`: `java -cp .:<path-to-JA> RunTranslator`

#### Output:

```
Hello World!
I'm the Main.main() method!
```

# Dynamic Proxy

Tramite la riflessione è possibile creare implementazioni dinamiche di interfacce a runtime, in particolare si utulizza la classe `java.lang.reflect.Proxy`.

I proxy dinamici vengono utilizzati quando un programma necessita di estendere o modificare alcune funzionalità di una classe già esistente. In questo caso, viene istanziato un oggetto proxy al posto di quello originale.

Durante il corso sono stati utilizzati per intercettare una chiamata ad un metodo ed eseguire delle istruzioni prima e/o dopo l'esecuzione del metodo chiamato. Volendo è possibile anche evitare che il metodo venga invocato.

Se si vuole "proxare" una classe è necessario che quest'ultima implementi un'interfaccia, questo perchè con il proxy può solo intercettare chiamate a metodi presenti nell'interfaccia.

Nel caso non fosse far implementare un'interfaccia alla classe che vogliamo "proxare", è possibile aggirare il problema creando classe "wrapper" che estende quella di cui vogliamo fare il proxy e che implementi l'interfaccia.

```java
public class ClasseWrapper extends ClasseDaProxare implements InterfacciaConIMetodiDaProxare {
	public ClasseWrapper() {
		super();
	}
}
```

Per creare un proxy bisogna utilizzare il metodo `Proxy.newProxyInstance()` che richiede i seguenti parametri:

-   Il class loader che deve "caricare" la classe del proxy
-   Un array di interfacce da implementare
-   Un `InvocationHandler` a cui inoltrare tutte le chiamate ai metodi del proxy

```java
import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Method;

public class TraceHandler implements InvocationHandler {
	Object target;

	public TraceHandler(Object target) {
		this.target = target;
	}

	@Override
	public Object invoke(Object proxy, Method method, Object[] args) throws Exception {
		try {
			System.out.println("Before calling the method");
			Object result = method.invoke(target, args);
			System.out.println("After  calling the method");
			return result;
		} catch (Exception e) {
            e.printStackTrace();
            return null;
        }
	}
}
```

```java
import java.lang.reflect.Proxy;

public class Main {
	public static void main(String[] args) throws Exception {
		InterfacciaConIMetodiDaProxare classe = new ClasseWrapper();
        InvocationHandler traceHandler = new TraceHandler(classe);

		var proxy = (InterfacciaConIMetodiDaProxare) Proxy.newProxyInstance(
			classe.getClass().getClassLoader(),
			classe.getClass().getInterfaces(),
			traceHandler);

		proxy.chiamataMetodoInterfaccia(); // Passerà attraverso l'invoke
	}
}
```

# Class Loading

Tutte le classi in Java vengono caricate utilizzando una sottoclasse di `java.lang.ClassLoader`, le classi vengono caricate on-demanda ovvero solo quando vengono effettivamente referenziate. Quando una classe viene caricata, vengono caricate anche tutte le classi a cui fa riferimento.

I class loader sono organizzati gerarchicamente e si basano su di un sistema di delegazione. Quando viene creato un nuovo `ClassLoader` è necessario fornirgli un `ClassLoader` padre. Se ad un `ClassLoader` viene chiesto di caricare una classe, chiederà a suo padre di caricarla. Se quest'ultimo non riesce a trovare la classe, il figlio proverà a caricarla da solo.

Per caricare una classe un `ClassLoader` deve:

-   Verificare se la classe è già stata caricata

-   Se non è stata caricata, chiedere al padre di caricarla

-   Se il padre non riesce a caricare la classe il figlio deve provare a caricarla

Come esempio vediamo un class loader che conta quante classi di Java e classi scritte da noi vengono caricate quando si lancia `Main.java`.

```java
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
            printCounters();
            return super.loadClass(className);
        } else {
            userClasses += 1;
            printCounters();
            return findClass(className);
        }
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
}
```

```java
public class Main {
    public static void main(String[] args) {
        var dummy = new Dummy();
        System.out.println("Hello World!");
    }
}
```

#### Compilazione:

```
javac *.java
java -Djava.system.class.loader=CounterClassLoader Main
```
