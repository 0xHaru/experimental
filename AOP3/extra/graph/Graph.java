package graph;

import java.util.ArrayList;
import java.util.List;

public class Graph<E extends Comparable<E>> {
    private class Vertex {
        public E data;
        public List<Vertex> neighbors;

        public Vertex(E data) {
            this.data = data;
            neighbors = new ArrayList<>();
        }

        public boolean addNeighbor(Vertex v) {
            for (Vertex neighbor : neighbors) {
                if (neighbor.data.compareTo(v.data) == 0)
                    return false; // the edge already exists
            }

            return neighbors.add(v); // this will return true
        }

        public boolean removeNeighbor(E e) {
            for (int i = 0; i < neighbors.size(); i += 1) {
                if (neighbors.get(i).data.compareTo(e) == 0) {
                    neighbors.remove(i);
                    return true;
                }
            }

            return false;
        }
    }

    private List<Vertex> vertices;

    public Graph() {
        vertices = new ArrayList<>();
    }

    public boolean removeEdge(E from, E to) {
        Vertex fromV = null;
        Vertex toV = null;

        for (Vertex v : vertices) {
            if (from.compareTo(v.data) == 0) { // see if from vertex already exists
                fromV = v;
            } else if (to.compareTo(v.data) == 0) { // see if from vertex already exists
                toV = v;
            }

            if (fromV != null && toV != null)
                break; // both vertices exist so stop searching
        }

        if (fromV == null || toV == null)
            return false;

        return fromV.removeNeighbor(to) && toV.removeNeighbor(from);
    }

    public boolean addEdge(E from, E to) {
        Vertex fromV = null;
        Vertex toV = null;

        for (Vertex v : vertices) {
            if (from.compareTo(v.data) == 0) { // see if from vertex already exists
                fromV = v;
            } else if (to.compareTo(v.data) == 0) { // see if from vertex already exists
                toV = v;
            }

            if (fromV != null && toV != null)
                break; // both vertices exist so stop searching
        }

        if (fromV == null) {
            fromV = new Vertex(from);
            vertices.add(fromV);
        }

        if (toV == null) {
            toV = new Vertex(to);
            vertices.add(toV);
        }

        return fromV.addNeighbor(toV) && toV.addNeighbor(fromV);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        for (Vertex v : vertices) {
            sb.append("[" + v.data + "] -> ");

            for (Vertex v2 : v.neighbors)
                sb.append(v2.data + " ");

            sb.append("\n");
        }

        if (sb.length() > 1)
            sb.deleteCharAt(sb.length() - 1);

        return sb.toString();
    }
}
