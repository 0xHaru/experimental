-module(ring).

-export([create_ring/1, send/1, stop/0]).

create_ring(Size) ->
    Pids = [spawn(fun() -> actor_init(Id, Size) end) || Id <- lists:seq(1, Size)],
    register(first_actor, hd(Pids)),
    connect_neighbors(lists:zip(Pids, tl(Pids) ++ [hd(Pids)])),
    io:format("Actors: ~p~n", [Pids]).

connect_neighbors([]) ->
    ok;
connect_neighbors([{CurrPid, NeighborPid} | Tail]) ->
    CurrPid ! {neighbor, NeighborPid},
    connect_neighbors(Tail).

actor_init(Id, RingSize) ->
    receive
        {neighbor, NeighborPid} ->
            actor_loop(Id, RingSize, NeighborPid)
    end.

actor_loop(Id, RingSize, NeighborPid) ->
    receive
        {msg, Msg} when Id =:= RingSize ->
            io:format("~p reached the last actor~n", [Msg]),
            actor_loop(Id, RingSize, NeighborPid);
        {msg, Msg} ->
            NeighborPid ! {msg, Msg},
            actor_loop(Id, RingSize, NeighborPid);
        stop ->
            NeighborPid ! stop
    end.

send(Msg) ->
    first_actor ! {msg, Msg},
    ok.

stop() ->
    first_actor ! stop,
    unregister(first_actor),
    ok.

% c(ring).
% ring:create_ring(5).
% ring:send("Hello World").
% ring:stop().
