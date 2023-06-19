-module(easyring).
-export([create_ring/1, send_message/1, stop/0]).

create_ring(NumOfActors) ->
    Pids = [spawn(fun() -> actor_init(Id, NumOfActors) end) || Id <- lists:seq(1, NumOfActors)],
    register(first_actor, hd(Pids)),
    send_init_msg(lists:zip(Pids, tl(Pids) ++ [hd(Pids)])).

send_init_msg([]) -> ok;
send_init_msg([{Curr, Next} | PidsT]) ->
    Curr ! {init, Next},
    send_init_msg(PidsT).

actor_init(Id, NumOfActors) ->
    receive
        {init, Next} ->
            io:format("Spawning actor ~p~n", [Id]),
            actor_loop(Id, NumOfActors, Next)
    end.

actor_loop(Id, NumOfActors, Next) ->
    receive
        {msg, From, Msg} when Id =:= NumOfActors ->
            io:format("~p reached the last actor ~p~n", [Msg, Id]),
            actor_loop(Id, NumOfActors, Next);
        {msg, From, Msg} ->
            io:format("~p passing through actor ~p~n", [Msg, Id]),
            Next ! {msg, self(), Msg},
            actor_loop(Id, NumOfActors, Next);
        stop -> Next ! stop
    end.


send_message(Msg) ->
    first_actor ! {msg, self(), Msg},
    ok.

stop() ->
    first_actor ! stop,
    unregister(first_actor),
    ok.

% > c(easyring).
% {ok,easyring}
%
% > easyring:create_ring(4).
% Spawning actor 1
% Spawning actor 2
% Spawning actor 3
% Spawning actor 4
% ok
%
% > easyring:send_message("Hello").
% "Hello" passing through actor 1
% "Hello" passing through actor 2
% "Hello" passing through actor 3
% "Hello" reached the last actor 4
% ok
%
% > easyring:stop().
% ok
