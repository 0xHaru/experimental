-module(patternmatching).
-export([start/0]).

start() ->
    Pid1 = spawn(fun() -> correct_way(10) end),
    Pid1 ! {example, 10},
    Pid1 ! {example, 1},
    Pid1 ! stop,

    Pid2 = spawn(fun() -> wrong_way(100) end),
    Pid2 ! {example, 100},
    Pid2 ! {example, 1},
    Pid2 ! stop,

    ok.

correct_way(N) ->
    receive
        {example, M} when N =:= M ->
            io:format("CORRECT WAY N == M (N = ~p,  M = ~p)~n", [N, M]),
            correct_way(N);
        {example, M} ->
            io:format("CORRECT WAY N != M (N = ~p,  M = ~p)~n", [N, M]),
            correct_way(N);
        stop -> stopping
    end.

wrong_way(N) ->
    receive
        {example, N} ->
            io:format("WRONG   WAY N == N (N = ~p, N = ~p)~n", [N, N]),
            wrong_way(N);
        {example, M} ->
            io:format("WRONG   WAY N != M (N = ~p, M = ~p)~n", [N, M]),
            wrong_way(N);
        stop -> stopping
    end.

% c(patternmatching).
% patternmatching:start().
%
% CORRECT WAY N == M (N = 10,  M = 10)
% CORRECT WAY N != M (N = 10,  M = 1)
% WRONG   WAY N == N (N = 100, N = 100)
% WRONG   WAY N != M (N = 100, M = 1)
