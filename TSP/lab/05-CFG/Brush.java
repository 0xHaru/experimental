public class Brush {
    private Painter owner;

    public Brush(Painter owner) {
        this.owner = owner;
    }

    public void dipInPaint() {

    }

    public void move() {

    }

    public void rinseWithWater() {

    }

    public void dry() {

    }

    @InvokedMethods({ "Painter.getName()" })
    public String getOwnerName() {
        return owner.getName();
    }
}
