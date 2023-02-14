public aspect DelegationCount percflow(delegated()) {
    pointcut delegated()
        : call(public * *(..))        &&
          !call(public * java..*(..)) &&
          !within(DelegationCount);

    static int count = 0;
    static int max = 0;

    before() : delegated() {
        System.out.println("BEFORE " + thisJoinPoint);

        count += 1;

        if(count > max)
            max = count;
    }

    after() : delegated() {
        System.out.println("AFTER  " + thisJoinPoint);

        count -= 1;

        if(count == 0) {
            System.out.println("The delegation level for " +
                               "\"" + thisJoinPoint + "\"" +
                               " is " + (max - 1));

            max = 0;
        }
    }
}
