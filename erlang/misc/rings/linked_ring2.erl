-module(linked_ring2).
-export([create_ring/1, send/1, stop/0]).

create_ring(Size) ->
    register(master, self()),
    FirstActor = spawn(fun() -> actor_loop(1, Size, null) end),
    register(first_actor, FirstActor),
    first_actor ! {spawn, Size - 1},
    receive
        done ->
            io:format("The ring has been created successfully~n")
    end.

actor_loop(Id, RingSize, NeighborPid) ->
    receive
        {spawn, 0} ->
            master ! done,
            actor_loop(Id, RingSize, NeighborPid);
        {spawn, Count} ->
            Pid = spawn_link(fun() -> actor_loop(Id + 1, RingSize, null) end),
            Pid ! {spawn, Count - 1},
            actor_loop(Id, RingSize, Pid);
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

% c(linked_ring).
% linked_ring2:create_ring(5).
% linked_ring2:send("Hello World").
% linked_ring2:stop().
