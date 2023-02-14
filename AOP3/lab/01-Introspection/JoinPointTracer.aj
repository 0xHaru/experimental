privileged public aspect JoinPointTracer {
    pointcut tracer() : !within(JoinPointTracer);

    before() : tracer() {
        System.out.println("[B]: " + thisJoinPoint);
    }

    after() : tracer() {
        System.out.println("[A]:  " + thisJoinPoint);
    }
}
