-module(ring).
-export([start/2, stop/0, send_message/1, send_message/2]).

start(NumOfActors, Funs) ->
    Pids = create_ring(NumOfActors, Funs, []),
    register(first_actor, hd(Pids)),
    register(last_actor, hd(lists:reverse(Pids))),

    io:format("~p - Ring: ~p~n", [self(), Pids]),

    % Link actors together
    lists:foreach(fun({From, To}) ->
        case From =:= whereis(last_actor) of
            true -> From ! {init, last, To};
            false -> From ! {init, To}
        end
    end, lists:zip(Pids, tl(Pids) ++ [hd(Pids)])).

create_ring(0, _, Pids) -> Pids;
create_ring(Count, [FunsH | FunsT], Pids) ->
    NewPid = spawn(fun() -> actor_init(FunsH) end),
    create_ring(Count - 1, FunsT, Pids ++ [NewPid]).

actor_init(Fun) ->
    receive
        {init, NextActor} ->
            link(NextActor),
            actor_loop(Fun, NextActor);
        {init, last, NextActor} ->
            link(NextActor),
            last_actor_loop(Fun, NextActor)
    end.

actor_loop(Fun, NextActor) ->
    % io:format("~p - Next Actor: ~p~n", [self(), NextActor]),
    receive
        quit ->
            NextActor ! quit,
            exit(quit);
        {task, Input, Times} ->
            % io:format("~p - Input: ~p  Time: ~p~n", [self(), Input, Times]),
            NextActor ! {task, Fun(Input), Times}
    end,
    actor_loop(Fun, NextActor).

last_actor_loop(Fun, NextActor) ->
    % io:format("~p - Next Actor: ~p | (LAST ACTOR)~n", [self(), NextActor]),
    receive
        quit ->
            NextActor ! quit,
            exit(quit);
        {task, Input, 1} ->
            io:format("~p - Result: ~p~n", [self(), Fun(Input)]);
        {task, Input, Times} ->
            % io:format("~p - Input: ~p  Time: ~p | (LAST ACTOR)~n", [self(), Input, Times]),
            NextActor ! {task, Fun(Input), Times - 1}
    end,
    last_actor_loop(Fun, NextActor).

stop() -> first_actor ! quit.

send_message(Input) ->
    send_message(Input, 1).

send_message(Input, Times) ->
    first_actor ! {task, Input, Times}.


