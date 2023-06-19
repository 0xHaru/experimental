public class Toolbox {
    private Painter owner;
    private Brush brush;

    public Toolbox(Painter owner, Brush brush) {
        this.owner = owner;
        this.brush = brush;
    }

    @InvokedMethods({ "Painter.getName()" })
    public String getOwnerName() {
        return owner.getName();
    }

    @InvokedMethods({ "Brush.getOwnerName()" })
    public String getBrushOwnerName() {
        return brush.getOwnerName();
    }
}
