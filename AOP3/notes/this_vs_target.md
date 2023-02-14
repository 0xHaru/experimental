# Difference between this() and target()

At a matching join point, `this()` is the **object you are in**, `target()` is the **object you are invoking/referencing.**

The confusion may arise because in the case of an `execution()` pointcut matching on a join point **they are the same thing** - the object containing the execution join point which matched is the same as the object running the method you are matching on.

But in the case of a `call()` join point **they are different**. The object making the call is different from the object on which the method is being called.

```java
class A {
  public void m() {
    B b = new B();
    b.n();
  }
}
class B {
  public void n() {
  }
}
```

For that setup, the pointcut `execution(* m(..))` will match on join point `A.m()` and have a `this(`) of type `A` and `target()` of type `A` (and they will be the same instance of `A`).

However the pointcut `call(* n(..))` will match at the call site in method `A.m()` where it calls `n()` and at that point `this()` will be the instance of `A` making the call whilst `target()` will be the instance of `B` that the method is being invoked upon.

Source: https://stackoverflow.com/questions/34305792/this-vs-target-aspectj
