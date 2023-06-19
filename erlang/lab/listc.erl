-module(listc).
-export([squared_int/1, intersect/2, symmetric_difference/2]).

% 1.
squared_int(Lst) ->
    [X * X || X <- Lst, is_integer(X)].

% listc:squared_int([1, hello, 100, boo, "boo", 9]). -> [1,10000,81]

% 2.
intersect(Lst1, Lst2) ->
    [X || X <- Lst1, lists:member(X, Lst2)].

% listc:intersect([1,2,3,4,5], [4,5,6,7,8]). -> [4,5]

% 3.
symmetric_difference(Lst1, Lst2) ->
    [X || X <- (Lst1 ++ Lst2), lists:member(X, Lst1) xor lists:member(X, Lst2)].

% listc:symmetric_difference([1,2,3,4,5], [4,5,6,7,8]). -> [1,2,3,6,7,8]
