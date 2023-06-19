public class Main {
    public static void main(String[] args) {
        System.out.println("I'm the Main.main() method!");
    }
}

// javac -cp .:../javassist/javassist.jar *.java
// jar -m MANIFEST.MF -f PremainAgent.jar -c PremainAgent.class
// java -cp .:../javassist/javassist.jar -javaagent:PremainAgent.jar Main
// rm -f *.class *.jar
