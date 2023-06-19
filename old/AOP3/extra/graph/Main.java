package graph;

public class Main {
    public static void main(String args[]) {
        Graph<Integer> graph = new Graph<>();
        graph.addEdge(1, 2);
        graph.addEdge(1, 5);
        graph.addEdge(2, 5);
        graph.addEdge(1, 2); // repetition
        graph.addEdge(2, 1); // repetition
        graph.addEdge(2, 3);
        graph.addEdge(3, 4);
        graph.addEdge(4, 1);
        graph.addEdge(2, 3); // repetition
        System.out.println(graph + "\n");
        graph.removeEdge(2, 3);
        graph.removeEdge(5, 1);
        graph.removeEdge(2, 3); // repetition
        graph.removeEdge(3, 2); // repetition
        graph.removeEdge(5, 4); // nonexistent edge
        System.out.println(graph);
    }
}
