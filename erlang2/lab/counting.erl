-module(counting).
-export([start/0, stop/0, tot/0, echo/1, succ/1, mul/2]).

start() ->
    ServerPid = spawn(fun() -> server_loop([]) end),
    io:format("~p - Server started: ~p~n", [self(), ServerPid]),
    register(server, ServerPid),
    ok.

stop() ->
    server ! shutdown,
    ok.

tot() ->
    ServerPid = whereis(server),
    server ! {self(), service, tot, null},
    receive
        {ServerPid, ok} -> ok;
        Any -> io:format("~p - Something went wrong: ~p~n", [self(), Any])
    end.

echo(Msg) ->
    ServerPid = whereis(server),
    server ! {self(), service, echo, Msg},
    receive
        {ServerPid, ok} -> ok;
        Any -> io:format("~p - Something went wrong: ~p~n", [self(), Any])
    end.

succ(X) ->
    ServerPid = whereis(server),
    server ! {self(), service, succ, X},
    receive
        {ServerPid, Result} -> Result;
        Any -> io:format("~p - Something went wrong: ~p~n", [self(), Any])
    end.

mul(X, Y) ->
    ServerPid = whereis(server),
    server ! {self(), service, mul, {X, Y}},
    receive
        {ServerPid, Result} -> Result;
        Any -> io:format("~p - Something went wrong: ~p~n", [self(), Any])
    end.

increment(Service, []) -> [{Service, 1}];
increment(Service, [{Service, Count} | T]) -> [{Service, Count + 1} | T];
increment(Service, [H | T]) -> [H | increment(Service, T)].

server_loop(Counters) ->
    receive
        shutdown ->
            io:format("~p - Server shutting down...~n", [self()]);
        {ClientPid, service, Service, Params} ->
            UpdatedCounters = increment(Service, Counters),
            case Service of
                tot ->
                    io:format("~p - Counters:~n", [self()]),
                    lists:foreach(fun(Counter) ->
                        io:format("~p~n", [Counter])
                    end, UpdatedCounters),
                    ClientPid ! {self(), ok},
                    server_loop(UpdatedCounters);
                echo ->
                    Msg = Params,
                    io:format("~p - ~p~n", [self(), Msg]),
                    ClientPid ! {self(), ok},
                    server_loop(UpdatedCounters);
                succ ->
                    X = Params,
                    ClientPid ! {self(), X + 1},
                    server_loop(UpdatedCounters);
                mul ->
                    {X, Y} = Params,
                    ClientPid ! {self(), X * Y},
                    server_loop(UpdatedCounters)
        end;
        Any ->
            io:format("~p - Invalid message: ~p~n", [self(), Any])
    end.
