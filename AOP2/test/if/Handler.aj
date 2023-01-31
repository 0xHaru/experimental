abstract aspect Handler {
    pointcut matchCons(String[] strings)
        : execution(public Dummy.new(..)) && args(strings);
}
