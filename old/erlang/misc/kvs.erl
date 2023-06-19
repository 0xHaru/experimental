% kvs = key value server
-module(kvs).
-export([start/0, store/2, lookup/1]).

start() ->
    ServerPid = spawn(fun() -> server_loop() end),
    register(kvs, ServerPid),
    io:format("~p - Server started: ~p~n", [self(), ServerPid]),
    ok.

store(Key, Val) ->
    io:format("~p - store(~p, ~p) | (CLIENT)~n", [self(), Key, Val]),
    rpc({store, Key, Val}).

lookup(Key) ->
    io:format("~p - lookup(~p) | (CLIENT)~n", [self(), Key]),
    rpc({lookup, Key}).

rpc(Query) ->
    io:format("~p - rpc(~p) | (CLIENT)~n", [self(), Query]),
    kvs ! {self(), Query},
    receive
        {kvs, Response} -> Response
    end.

server_loop() ->
    receive
        {ClientPid, {store, Key, Val}} ->
            io:format("~p - {store, ~p, ~p}} | (SERVER)~n", [self(), Key, Val]),
            put(Key, Val),
            ClientPid ! {kvs, done},
            server_loop();
        {ClientPid, {lookup, Key}} ->
            io:format("~p - {lookup, ~p}} | (SERVER)~n", [self(), Key]),
            ClientPid ! {kvs, get(Key)},
            server_loop()
    end.

% FOO
% erl -sname foo
% kvs:start().
% kvs:store(italy, rome).

% BAR
% erl -sname bar
% rpc:call(foo@lab, kvs, lookup, [italy]).
