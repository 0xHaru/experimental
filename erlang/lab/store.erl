-module(store).
-export([connect_to/1, store/2, lookup/1]).

connect_to(Hostnames) ->
    NodePids = lists:map(fun(Hostname) ->
        case net_kernel:connect_node(Hostname) of
            true ->
                io:format("~p - Connected to \"~p\"~n", [self(), Hostname]),
                spawn(Hostname, fun() -> server_loop(true) end);
            false ->
                io:format("~p - Failed to connect to \"~p\"~n", [self(), Hostname]);
            ignored ->
                io:format("~p - \"~p\" is not alive~n", [self(), Hostname])
        end
    end, Hostnames),
    put(nodes, NodePids),
    NodePids.

random_node(Nodes) ->
    lists:nth(rand:uniform(length(Nodes)), Nodes).

store(Key, Val) ->
    io:format("~p - store(~p, ~p) | (CLIENT)~n", [self(), Key, Val]),
    NodePids = get(nodes),
    lists:foreach(fun(NodePid) ->
        rpc(NodePid, {store, Key, Val})
    end, NodePids).

lookup(Key) ->
    io:format("~p - lookup(~p) | (CLIENT)~n", [self(), Key]),
    NodePid = random_node(get(nodes)),
    rpc(NodePid, {lookup, Key}).

rpc(NodePid, Query) ->
    io:format("~p - rpc(~p) | (CLIENT)~n", [self(), Query]),
    NodePid ! {self(), Query},
    receive
        {NodePid, Response} -> Response
    end.

server_loop(FirstCall) ->
    case FirstCall of
        true -> io:format("~p - Server is running on \"~p\"~n", [self(), node()]);
        false -> void
    end,
    receive
        {ClientPid, {store, Key, Val}} ->
            io:format("~p - {store, ~p, ~p} | (SERVER)~n", [self(), Key, Val]),
            put(Key, Val),
            ClientPid ! {self(), done},
            server_loop(false);
        {ClientPid, {lookup, Key}} ->
            io:format("~p - {lookup, ~p} | (SERVER)~n", [self(), Key]),
            ClientPid ! {self(), get(Key)},
            server_loop(false)
    end.

% erl -sname main@localhost -setcookie cookie
% erl -sname foo@localhost -setcookie cookie
% erl -sname bar@localhost -setcookie cookie

% MAIN
% c(store).
% store:connect_to([foo@localhost, bar@localhost]).
% nodes().

% FOO
% nodes().

% BAR
% nodes().

% MAIN
% store:store(italy, rome).
% store:lookup(italy).
