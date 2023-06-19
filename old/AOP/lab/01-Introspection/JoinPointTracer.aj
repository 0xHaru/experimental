public aspect JoinPointTracer {
    pointcut tracer() : !within(JoinPointTracer);

    before() : tracer() {
        System.out.println("BEFORE: " + thisJoinPoint);
    }

    after() : tracer() {
        System.out.println("AFTER:  " + thisJoinPoint);
    }
}
