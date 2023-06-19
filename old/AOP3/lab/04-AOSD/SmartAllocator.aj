public aspect SmartAllocator {
    private ResourceManager manager = new ResourceManager();

    pointcut objectCreation() : call(public Resource+.new(..));

    pointcut objectDestruction(Resource resource)
        : execution(public void Resource+.destroy()) && this(resource);

    pointcut exclude()
        : !within(Resource)        &&
          !within(ResourceManager) &&
          !within(SmartAllocator);

    Object around() : objectCreation() && exclude() {
        String type = thisJoinPoint.getSignature().getDeclaringTypeName();

        if(!manager.isEmpty(type)) {
            System.out.println("*** I'm pooling a " + type + " instance");
            return manager.getResource(type);
        }

        return proceed();
    }

    before(Resource resource) : objectDestruction(resource) && exclude() {
        System.out.println("*** I'm storing a " + resource.getClass().getName() + " instance");
        manager.releaseResource(resource.getClass().getName(), resource);
    }
}
