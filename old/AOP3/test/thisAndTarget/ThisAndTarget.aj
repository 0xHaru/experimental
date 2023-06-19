public aspect ThisAndTarget {
    pointcut trackA() : call(* *.m(..)) && this(Main) && target(A);

    pointcut trackB() : call(* *.n(..)) && this(A) && target(B);

    before() : trackA() {
        System.out.println("before trackA()");
    }

    before() : trackB() {
        System.out.println("before trackB()");
    }
}
