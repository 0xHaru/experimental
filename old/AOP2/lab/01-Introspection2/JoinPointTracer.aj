privileged public aspect JoinPointTracer {
    pointcut call_() : call(* *.*(..));

    pointcut exec() : execution(* *.*(..));

    pointcut ccons() : call(*.new(..));

    pointcut econs() : execution(*.new(..));

    pointcut set_() :  set(* *.*);

    pointcut get_() :  get(* *.*);

    pointcut init() : initialization(*.new(..));

    pointcut pinit() : preinitialization(*.new(..));

    pointcut sinit() : staticinitialization(*);

    pointcut catch_() : handler(*);

    pointcut all() : (call_() || exec()  ||
                      ccons() || econs() ||
                      get_()  || set_()  ||
                      init()  || pinit() || sinit()) && !within(JoinPointTracer);

    before() : all() || catch_() {
        System.out.println("[B]: " + thisJoinPoint);
    }

    after() : all() {
        System.out.println("[A]: " + thisJoinPoint);
    }
}
