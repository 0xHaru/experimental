-module(generator).
-export([init/0]).

init() ->
    receive
        {init, From, Len, Elems, Rep} ->
            Col = column(Len, Elems, Elems, Rep, []),
            From ! {column, Rep, Col}
    end.

column(0, _, _, _, Acc) ->
    Acc;
column(Len, Elems, [], Rep, Acc) ->
    column(Len, Elems, Elems, Rep, Acc);
column(Len, Elems, [Elem | T], Rep, Acc) ->
    Chunk = lists:duplicate(Rep, Elem),
    column(Len - Rep, Elems, T, Rep, Acc ++ Chunk).
