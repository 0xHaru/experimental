import java.util.Hashtable;
import java.util.Vector;

public class ResourceManager implements ResourcePool {
    private Hashtable<String, Vector<Resource>> pool = new Hashtable<>();

    public boolean isEmpty(String type) {
        Vector<Resource> resourceList = pool.get(type);
        return (resourceList == null) || (resourceList.size() == 0);
    }

    public Resource getResource(String type) {
        Vector<Resource> resourceList = pool.get(type);
        Resource resource = resourceList.remove(0);
        pool.put(type, resourceList);
        return resource;
    }

    public void releaseResource(String type, Resource resource) {
        Vector<Resource> resourceList = pool.get(type);

        if (resourceList == null)
            resourceList = new Vector<Resource>();

        resourceList.addElement(resource);
        pool.put(type, resourceList);
    }
}

// Hashtable and Vector are synchronized and thread safe,
// on the other hand Hashmap and ArrayList are NOT thread safe!
