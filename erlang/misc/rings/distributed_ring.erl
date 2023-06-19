-module(distributed_ring).
-export([create_ring/1, actor_init/2, send/1, stop/0]).

create_ring(ShortNames) ->
    {ok, Hostname} = inet:gethostname(),
    Nodes = [list_to_atom(Name ++ "@" ++ Hostname) || Name <- ShortNames],
    Pids = [spawn(Node, distributed_ring, actor_init, [Id, length(Nodes)])
            || {Id, Node} <- lists:enumerate(1, Nodes)],
    global:register_name(first_actor, hd(Pids)),
    connect_neighbors(lists:zip(Pids, tl(Pids) ++ [hd(Pids)])),
    io:format("The master process spawned: ~p~n", [Pids]).

connect_neighbors([]) -> ok;
connect_neighbors([{CurrPid, NeighborPid} | Tail]) ->
    CurrPid ! {neighbor, NeighborPid},
    connect_neighbors(Tail).

% It MUST be explicitly exported otherwise spawn(Node, Mod, Func, Args) will fail
actor_init(Id, RingSize) ->
    group_leader(whereis(user), self()), % Very important!
    receive
        {neighbor, NeighborPid} ->
            io:format("Spawning actor ~p~n", [Id]),
            actor_loop(Id, RingSize, NeighborPid)
    end.

actor_loop(Id, RingSize, NeighborPid) ->
    receive
        {msg, Msg} when Id =:= RingSize ->
            io:format("~p reached the last actor ~p~n", [Msg, Id]),
            actor_loop(Id, RingSize, NeighborPid);
        {msg, Msg} ->
            io:format("~p passing through actor ~p~n", [Msg, Id]),
            NeighborPid ! {msg, Msg},
            actor_loop(Id, RingSize, NeighborPid);
        stop ->
            io:format("Actor ~p is shutting down...~n", [Id]),
            NeighborPid ! stop
    end.

send(Msg) ->
    global:whereis_name(first_actor) ! {msg, Msg},
    ok.

stop() ->
    global:whereis_name(first_actor) ! stop,
    global:unregister_name(first_actor),
    ok.

% erl -sname one
% erl -sname two
% erl -sname three
% erl -sname master

% c(distributed_ring).
% distributed_ring:create_ring(["one", "two", "three"]).
% distributed_ring:send("test").
% distributed_ring:stop().

% CANT SPAWN NON EXPORTED FUNCTIONS ON OTHER NODES

% REQUESTING THE PID
