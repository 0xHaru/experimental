public aspect Pertarget pertarget(matchCons()) {
    pointcut matchCons()
        : execution(public Dummy.new(..));

    before() : matchCons() {
        System.out.println("Before: " + thisJoinPoint);
    }
}
