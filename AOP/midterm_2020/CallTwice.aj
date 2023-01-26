import java.util.*;
import java.lang.reflect.*;

public aspect CallTwice pertarget(methodCall()) {
    private final HashMap<String, List<Object>> map = new HashMap<>();

    pointcut methodCall()
        : call(void *..*(..))  &&
          !call(* java..*(..)) &&
          !within(CallTwice);

    void around(Object o) : methodCall() && target(o) {
        String name = thisJoinPointStaticPart.getSignature().toString();

        if(map.containsKey(name)) {
            Object[] newArgs = thisJoinPoint.getArgs();
            Object[] oldArgs = map.get(name).toArray(Object[]::new);
            Class[] classes = new Class[newArgs.length];

            for(int i = 0; i < newArgs.length; ++i) {
                if(newArgs[i].getClass().equals(String.class)) {
                    newArgs[i] = ((String)oldArgs[i]) + ((String)newArgs[i]);
                    classes[i] = String.class;
                } else if(newArgs[i].getClass().equals(Integer.class)) {
                    newArgs[i] = ((int)oldArgs[i]) + ((int)newArgs[i]);
                    classes[i] = int.class;
                } else {
                    throw new TypeException(newArgs.getClass().getName() + " not support + operator");
                }
            }

            map.remove(name);
            Class cls = thisJoinPoint.getSignature().getDeclaringType();

            try {
                Method m = cls.getMethod(thisJoinPoint.getSignature().getName(), classes);
                m.invoke(o, newArgs);
            } catch (Exception ex) {
                throw new RunException(ex);
            }
        } else {
            map.put(name, Arrays.asList(thisJoinPoint.getArgs()));
        }
    }
}

class TypeException extends RuntimeException {
    public TypeException(String msg) {
        super(msg);
    }
}

class RunException extends RuntimeException {
    public RunException(Throwable ex) {
        super(ex);
    }
}
