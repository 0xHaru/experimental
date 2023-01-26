public aspect CallExec {
    pointcut onCall(Dummy d, int x)
        : call(* *.*(..)) &&
          target(d)       &&
          args(x);

    pointcut onExecution(Dummy d, int x)
        : execution(* *.*(..)) &&
          target(d)            &&
          args(x);

    before(Dummy d, int x): onCall(d, x) {
        System.out.println("before::onCall");
        System.out.println("Target: " + d);
        System.out.println("Args: " + x);
    }

    after(Dummy d, int x): onCall(d, x) {
        System.out.println("after::onCall");
    }

    before(Dummy d, int x): onExecution(d, x) {
        System.out.println("before::onExecution");
    }


    after(Dummy d, int x): onExecution(d, x) {
        System.out.println("after::onExecution");
    }
}
