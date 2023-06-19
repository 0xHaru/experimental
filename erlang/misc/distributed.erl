-module(distributed).
-export([start/1, rpc/4]).

start(Node) ->
    NodePid = spawn(Node, fun() -> loop() end),
    io:format("~p - Spawned a new node: ~p~n", [self(), NodePid]),
    ok.

rpc(Pid, Module, Func, Args) ->
    Pid ! {rpc, self(), Module, Func, Args},
    receive
        {Pid2, Response} when Pid2 =:= Pid -> Response
    end.

loop() ->
    receive
        {rpc, Pid, Module, Func, Args} ->
            Pid ! {self(), (catch apply(Module, Func, Args))},
            loop()
    end.


% FOO
% erl -sname foo -setcookie cookie

% BAR
% erl -sname bar -setcookie cookie

% FOO
% Pid = distributed:start(bar@lab).
% node().
% distributed:rpc(Pid, erlang, node, []).
