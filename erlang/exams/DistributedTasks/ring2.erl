-module(ring2).
-export([start/2, send_message/1, send_message/2, stop/0]).

% Creates the actors ring, registers the first actor and initializes the actors
start(NumOfActors, Funs) ->
    Pids = [spawn(fun() -> actor_init(Id, NumOfActors) end) || Id <- lists:seq(1, NumOfActors)],
    register(first_actor, hd(Pids)),
    NextPids = lists:zip(Pids, tl(Pids) ++ [hd(Pids)]),
    send_init_msg(NextPids, Funs).

% Sends a stop message to the first actor who in turn will relay it to his neighbor and so on...
stop() ->
    first_actor ! stop,
    unregister(first_actor).

send_message(Input) -> send_message(Input, 1).

% Send the input and the number of loops to the first actor
send_message(Input, Loops) ->
    first_actor ! {compute, Input, Loops},
    ok.

% Called in the start function to initialize the actors with their neighbor and function
send_init_msg([], []) -> ok;
send_init_msg([{Curr, Next} | PidsT], [Fun | FunsT]) ->
    Curr ! {init, Next, Fun},
    send_init_msg(PidsT, FunsT).

actor_init(Id, NumOfActors) ->
    receive
        {init, Next, Fun} -> actor_loop(Id, NumOfActors, Next, Fun)
    end.

% Id = position in the ring, Next = PID of his next neighbor
actor_loop(Id, NumOfActors, Next, Fun) ->
    receive
        % We reached the last actor and it's the final loop, print out the result
        {compute, Input, Loops} when Id =:= NumOfActors, Loops =:= 0 ->
            io:format("~p~n", [Fun(Input)]),
            actor_loop(Id, NumOfActors, Next, Fun);

        % We are passing through the first actor, decrease the loop count
        {compute, Input, Loops} when Id =:= 1 ->
            Next ! {compute, Fun(Input), Loops - 1},
            actor_loop(Id, NumOfActors, Next, Fun);

        % Relay the partial result to his neighbor
        {compute, Input, Loops} ->
            Next ! {compute, Fun(Input), Loops},
            actor_loop(Id, NumOfActors, Next, Fun);

        % Relay the stop message to his neighbor
        stop -> Next ! stop
    end.
