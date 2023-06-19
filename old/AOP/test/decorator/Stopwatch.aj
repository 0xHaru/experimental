public aspect Stopwatch {
    pointcut heavyComputation()
        : call(* *.*Computation*(..)) &&
          !within(Stopwatch);

    Object around() : heavyComputation() {
        long start = System.currentTimeMillis();
        Object result = proceed();
        long end =  System.currentTimeMillis();

        System.out.println(thisJoinPoint + " -> " + (end - start) + "ms");
        return result;
    }
}
