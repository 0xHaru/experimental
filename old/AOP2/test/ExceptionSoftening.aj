import org.aspectj.lang.SoftException;

aspect SmartExceptionHandlingAspect {
	declare soft : Exception
		: (call(* *.*(..) throws *)) && !within(SmartExceptionHandlingAspect);
		
	declare soft : Exception
		: (call(public *.new(..) throws *)) && !within(SmartExceptionHandlingAspect);
		
	after() throwing(SoftException ex) : execution(* *.*(..)) {
		Throwable t = ex.getWrappedThrowable();
		StackTraceElement[] ste = t.getStackTrace();
		
		System.out.println("In class "+ste[0].getClassName() +
			" (file "+ste[0].getFileName()+") method "+ste[0].getMethodName() +
			" at row "+ste[0].getLineNumber()+" has raised a "+t.getClass()+" exception.");
			
		System.exit(0);
	}
}
