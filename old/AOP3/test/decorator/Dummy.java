public class Dummy {
    public void doHeavyComputation() throws InterruptedException {
        Thread.sleep(3000);
    }

    public static void main(String[] args) {
        try {
            Dummy d = new Dummy();
            d.doHeavyComputation();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}

// ajc -1.9 Dummy.java Stopwatch.aj
// aj Main
// rm -f *.class
