-module(mm).
-export([init/2]).

init(Id, Server) ->
    group_leader(whereis(user), self()),
    io:format("~p is running~n", [Id]),
    mm_loop(Id, Server).

mm_loop(Id, Server) ->
    receive
        Msg ->
            io:format("[~p] forwarding ~p~n", [Id, Msg]),
            Server ! {Id, Msg}, % Server ! {mm_, {Index, Lst, Size, E}}
            mm_loop(Id, Server)
    end.

