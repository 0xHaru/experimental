public class TrafficLight {
    private Colors state;

    public TrafficLight() {
        state = Colors.Green;
    }

    public void go() {
        state = Colors.next(state);
    }

    public Colors getColor() {
        return state;
    }

    public void setColor(Colors c) {
        state = c;
    }
}
