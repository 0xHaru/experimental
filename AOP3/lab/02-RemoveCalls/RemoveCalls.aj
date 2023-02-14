import org.aspectj.lang.reflect.SourceLocation;

public aspect RemoveCalls {
    /* Capture every call to a method of A that occurs in the control flow of a method of B
       and exclude the ones that occur in the control flow of a method of C */
    pointcut callsToRemove()
        : cflow(call(* B.*(..)))  &&
          !cflow(call(* C.*(..))) &&
          call(* A.*(..))         &&
          !within(RemoveCalls);

    void around() : callsToRemove() {
        SourceLocation loc = thisJoinPoint.getSourceLocation();
        System.out.println("Skipping \"" + thisJoinPoint + "\" at " + loc);
    }
}
