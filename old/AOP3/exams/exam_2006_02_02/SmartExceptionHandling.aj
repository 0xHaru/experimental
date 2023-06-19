import org.aspectj.lang.SoftException;

aspect SmartExceptionHandling {
    declare soft : Exception
        : (call(* *.*(..) throws *))       &&
          !within(SmartExceptionHandling);

    declare soft : Exception
        : (call(public *.new(..) throws *) &&
          !within(SmartExceptionHandling));

    after() throwing(SoftException e) : execution(* *.*(..)) {
        Throwable t = e.getWrappedThrowable();
        StackTraceElement[] ste = t.getStackTrace();

        String className  = ste[0].getClassName();
        String fileName   = ste[0].getFileName();
        String methodName = ste[0].getMethodName();
        int lineNumber    = ste[0].getLineNumber();

        String exceptionClass = t.getClass().toString().split(" ")[1];

        System.out.println("[" + fileName + ":" + lineNumber + "] - " +
                           className + "." + methodName +
                           "() raised " + exceptionClass);

        System.exit(0);
    }
}
