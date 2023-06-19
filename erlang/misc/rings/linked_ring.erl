-module(linked_ring).
-export([create_ring/1, send/1, stop/0]).

create_ring(Size) ->
    Pids = [spawn(fun() -> actor_init(Id, Size) end) || Id <- lists:seq(1, Size)],
    io:format("Actors: ~p~n", [Pids]),
    register(first_actor, hd(Pids)),
    connect_neighbors(lists:zip(Pids, tl(Pids) ++ [hd(Pids)])),
    first_actor ! link,
    ok.

connect_neighbors([]) -> ok;
connect_neighbors([{CurrPid, NeighborPid} | Tail]) ->
    CurrPid ! {neighbor, NeighborPid},
    connect_neighbors(Tail).

actor_init(Id, RingSize) ->
    receive
        {neighbor, NeighborPid} ->
            io:format("Spawning actor ~p~n", [Id]),
            actor_loop(Id, RingSize, NeighborPid)
    end.

actor_loop(Id, RingSize, NeighborPid) ->
    receive
        link ->
            link(NeighborPid),
            NeighborPid ! link,
            actor_loop(Id, RingSize, NeighborPid);
        {msg, Msg} when Id =:= RingSize ->
            io:format("~p reached the last actor~n", [Msg]),
            actor_loop(Id, RingSize, NeighborPid);
        {msg, Msg} ->
            NeighborPid ! {msg, Msg},
            actor_loop(Id, RingSize, NeighborPid)
    end.

send(Msg) ->
    first_actor ! {msg, Msg},
    ok.

stop() ->
    exit(whereis(first_actor), stopped),
    unregister(first_actor),
    ok.
