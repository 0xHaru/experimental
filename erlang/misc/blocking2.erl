-module(blocking2).
-export([add/2]).

add(X, Y) ->
    Result = addition(X, Y),
    io:format("~p - addition(~p, ~p) has returned~n", [self(), X, Y]),
    io:format("~p - Result: ~p~n", [self(), Result]).

addition(X, Y) ->
    io:format("~p - addition(~p, ~p) has started~n", [self(), X, Y]),
    timer:sleep(2000),
    X + Y.
