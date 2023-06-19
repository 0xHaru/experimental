public class Edge {
    private String sourceNode;
    private String destNode;
    private String methodName;

    public Edge(String sourceNode, String destNode, String methodName) {
        this.sourceNode = sourceNode;
        this.destNode = destNode;
        this.methodName = methodName;
    }

    public String toString() {
        String methodName = this.methodName.split("\\.")[1];
        methodName = methodName.substring(0, methodName.length() - 2);
        return sourceNode + " --( " + methodName + " )--> " + destNode;
    }
}
