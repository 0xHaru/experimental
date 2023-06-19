public class Painter {
    private String name;
    private Brush brush;
    private Toolbox toolbox;

    public Painter(String name, Brush brush, Toolbox toolbox) {
        this.name = name;
        this.brush = brush;
        this.toolbox = toolbox;
    }

    @InvokedMethods({ "Brush.rinseWithWater()", "Brush.dry()" })
    public void cleanUp() {
        brush.rinseWithWater();
        brush.dry();
    }

    @InvokedMethods({ "Brush.dipInPaint()", "Brush.move()", "Painter.cleanUp()" })
    public void paintSomething() {
        brush.dipInPaint();
        brush.move();
        cleanUp();
    }

    private void takeABreak(String reason) {

    }

    @InvokedMethods({ "Painter.takeABreak()" })
    public void lunchBreak() {
        takeABreak("lunchtime");
    }

    public String getName() {
        return name;
    }
}
