-module(combinator).
-export([start/2]).

start(M, N) ->
    Pids = spawn_slaves(M, []),

    ColumnLen = trunc(math:pow(N, M)),
    Elems = lists:seq(1, N),
    Freq = {N, 0},
    init_columns(ColumnLen, Elems, Freq, Pids),

    Columns = wait_columns(M, []),

    SortedColumns = lists:sort(fun ({Freq1, _}, {Freq2, _}) ->
        Freq1 > Freq2
    end, Columns),

    ExtractedColumns = lists:map(fun ({_, Column}) ->
        Column
    end, SortedColumns),

    Permutations = build_permutations(ExtractedColumns),
    print_permutations(Permutations).


spawn_slaves(0, Pids) -> Pids;
spawn_slaves(Count, Pids) ->
    Pid = spawn(fun() -> generator:column_init() end),
    spawn_slaves(Count - 1, Pids ++ [Pid]).


init_columns(_, _, _, []) -> ok;
init_columns(Length, Elems, {Base, Exp}, [Pid | T]) ->
    Freq = trunc(math:pow(Base, Exp)),
    Pid ! {init, self(), Length, Elems, Freq},
    init_columns(Length, Elems, {Base, Exp + 1}, T).


wait_columns(0, Cols) -> Cols;
wait_columns(N, Cols) ->
    receive
        {column, Freq, Col} ->
            wait_columns(N - 1, Cols ++ [{Freq, Col}])
    end.


build_permutations([[] | _]) -> [];
build_permutations(Columns) ->
    Combination = lists:foldr(fun (X, Acc) ->
        [X | Acc]
    end, [], lists:map(fun hd/1, Columns)),
    Other = build_permutations(lists:map(fun tl/1, Columns)),
    [Combination | Other].


print_permutations([]) -> ok;
print_permutations([Row | Rest]) ->
    lists:foreach(fun(Elem) ->
        io:format("~p  ", [Elem])
    end, Row),
    io:format("~n"),
    print_permutations(Rest).
