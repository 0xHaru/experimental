Official documentation: https://www.eclipse.org/aspectj/doc/released/

## General

AspectJ extends Java by overlaying a concept of join points onto the existing Java semantics and adding a few new program elements to Java:

A join point is a well-defined point in the execution of a program. These include method and constructor calls, field accesses and others described below.

A pointcut picks out join points, and exposes some of the values in the execution context of those join points. There are several primitive pointcut designators, and others can be named and defined by the pointcut declaration.

A piece of advice is code that executes at each join point in a pointcut. Advice has access to the values exposed by the pointcut. Advice is defined by before, after, and around declarations.

Inter-type declarations form AspectJ's static crosscutting features, that is, is code that may change the type structure of a program, by adding to or extending interfaces and classes with new fields, constructors, or methods. Some inter-type declarations are defined through an extension of usual method, field, and constructor declarations, and other declarations are made with a new declare keyword.

An aspect is a crosscutting type that encapsulates pointcuts, advice, and static crosscutting features. By type, we mean Java's notion: a modular unit of code, with a well-defined interface, about which it is possible to do reasoning at compile time. Aspects are defined by the aspect declaration.

## Cflow

Another pointcut, cflow, identifies join points based on whether they occur in the dynamic context of other join points. So

cflow(move())
picks out each join point that occurs in the dynamic context of the join points picked out by move(), our named pointcut defined above. So this picks out each join points that occurrs between when a move method is called and when it returns (either normally or by throwing an exception).

## Aspect instantiation

By default, each aspect is a singleton, so one aspect instance is created. This means that advice may use non-static fields of the aspect, if it needs to keep state around.

https://www.eclipse.org/aspectj/doc/released/progguide/semantics-aspects.html#aspect-instantiation
