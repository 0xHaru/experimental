public class CrossRoad {
    private TrafficLight[] tls;
    private String name;

    public CrossRoad(String n, TrafficLight[] tls) {
        this.tls = (TrafficLight[]) tls.clone();
        name = n;
    }

    public TrafficLight[] trafficlights() {
        return tls;
    }

    public void go() {
        for (TrafficLight tl : tls)
            tl.go();
    }

    public String toString() {
        String tmp = name + "\t";

        for (int i = 0; i < tls.length; i++)
            tmp += "TL(" + i + ") :- " + tls[i].getColor() + "\t";

        return tmp;
    }

    public static void main(String[] args) {
        CrossRoad cr1 = new CrossRoad("P.le Lodi",
                new TrafficLight[] {
                        new TrafficLight(), new TrafficLight(), new TrafficLight()
                });

        CrossRoad cr2 = new CrossRoad("P.le G. Piola",
                new TrafficLight[] {
                        new TrafficLight(), new TrafficLight(), new TrafficLight(), new TrafficLight()
                });

        for (int i = 1; i < 10; i++) {
            System.out.println(cr1);
            cr1.go();
        }

        System.out.println();

        for (int i = 1; i < 10; i++) {
            System.out.println(cr2);
            cr2.go();
        }
    }
}
