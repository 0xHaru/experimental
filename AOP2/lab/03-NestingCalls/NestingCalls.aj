public aspect NestingCalls {
    pointcut intToIntFunc(int n)
        : call(* Dummy.*(int)) &&
          args(n)              &&
          !within(NestingCalls);

    int around(int n) : intToIntFunc(n) {
        return proceed(proceed(n));
    }
}
