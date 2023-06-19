-module(hebrew).
-export([start/2]).

start(Id, K) ->
    receive
        {next, Next, master, Master} ->
            loop(Master, Id, K, Next);
        Any ->
            io:format("Error: ~p~n", [Any])
    end.

loop(Master, Id, K, Next) ->
    receive
        % The node next to you has died, the next next node will replace it
        {newNext, NewNext} ->
            loop(Master, Id, K, NewNext);
        % You are the survivor, notify the master
        {from, _, alive, 1, k, 1} ->
            Master ! {done, from, self(), id, Id};
        % You died
        {from, Prev, alive, Alive, k, CurrK} when CurrK =:= K ->
            Prev ! {newNext, Next},
            Next ! {from, Prev, alive, Alive - 1, k, 1};
        % Forward the message
        {from, _, alive, Alive, k, CurrK} ->
            Next ! {from, self(), alive, Alive, k, CurrK + 1},
            loop(Master, Id, K, Next)
    end.
