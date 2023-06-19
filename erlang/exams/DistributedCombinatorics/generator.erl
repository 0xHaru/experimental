-module(generator).
-export([column_init/0]).

% Each column is identified by its unique repetition frequency of each element
column_init() ->
    receive
        {init, From, Length, Elems, Freq} ->
            Col = column(Length, Elems, Elems, Freq, []),
            From ! {column, Freq, Col}
    end.


column(0, _, _, _, Col) -> Col;

column(Length, Elems, [], Freq, Col) ->
    column(Length, Elems, Elems, Freq, Col);

column(Length, Elems, [Elem | ElemsTL], Freq, Col) ->
    Chunk = lists:duplicate(Freq, Elem),
    column(Length - Freq, Elems, ElemsTL, Freq, Col ++ Chunk).
