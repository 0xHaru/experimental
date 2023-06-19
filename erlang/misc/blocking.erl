-module(blocking).
-export([blocking/0, not_blocking/0, proc/0]).

blocking() ->
    NewPid = spawn(?MODULE, proc, []),
    io:format("~p - Creating new process: ~p~n", [self(), NewPid]),
    NewPid ! self(),
    receive
        terminate -> io:format("~p - TERMINATE received~n", [self()]), void
    end,
    io:format("~p - Terminating...~n", [self()]).

not_blocking() ->
    NewPid = spawn(?MODULE, proc, []),
    io:format("~p - Creating new process: ~p~n", [self(), NewPid]),
    NewPid ! self(),
    % receive
    %     terminate -> io:format("~p - TERMINATE received~n", [self()]), void
    % end,
    io:format("~p - Terminating...~n", [self()]).

proc() ->
    receive
        ParentPid ->
            io:format("~p - ParentPid (~p) received~n", [self(), ParentPid]),
            timer:sleep(2000),
            ParentPid ! terminate
    end.
