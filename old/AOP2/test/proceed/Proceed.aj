public aspect Proceed {
    pointcut proc(int x)
        : call(public void Dummy.dummy(int)) &&
          args(x);

    void around(int x) : proc(x) {
        proceed(100);
    }
}
