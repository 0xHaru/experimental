import java.lang.reflect.Method;
import org.aspectj.lang.reflect.MethodSignature;

public aspect MethodSig {
    pointcut methodSig() : call(* Dummy.*(..));

    Object around() : methodSig() {
        System.out.println(thisJoinPoint.getSignature());
        System.out.println(thisJoinPointStaticPart.getSignature());

        Method m = ((MethodSignature) thisJoinPoint.getSignature()).getMethod();
        System.out.println(m);

        return proceed();
    }
}
