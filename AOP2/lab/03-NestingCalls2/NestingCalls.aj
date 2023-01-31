privileged public aspect NestingCalls {
    /*
       I want to match the return type but it's not allowed to do
       something like: * int Dummy.*(int), the access modifier is always required.
       So I match all public and !public methods instead.
    */
    pointcut intToIntFunc(int n)
        : (call(public int Dummy.*(int))   ||
           call(!public int Dummy.*(int))) &&
           args(n) &&
           !within(NestingCalls);


    int around(int n) : intToIntFunc(n) {
        return proceed(proceed(n));
    }
}
