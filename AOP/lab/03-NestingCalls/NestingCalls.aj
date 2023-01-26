public aspect NestingCalls {
    pointcut intToIntFunctions(int n)
        : call(* Dummy.*(int)) &&
          args(n)              &&
          !within(NestingCalls);

    int around(int n) : intToIntFunctions(n) {
        return proceed(proceed(n));
    }
}
