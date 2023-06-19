-module(combinator).
-export([start/2]).

%                           M  N
% EXAMPLE: combinator:start(2, 3)
%
% M = number of repetitions and columns
% N = possible values e.g. N = 3 -> [1,2,3]
start(M, N) ->
    ColumnLen = trunc(math:pow(N, M)),
    Elems = lists:seq(1, N),
    % Spawn the slaves
    Slaves = [spawn(generator, init, []) || _ <- lists:seq(1, M)],
    % Generate the list of repetitions -> Reps = [3^0, 3^1]
    Reps = [trunc(math:pow(N, Exp)) || Exp <- lists:seq(0, M - 1)],
    % Initialize the slaves
    init_slaves(Slaves, ColumnLen, Elems, Reps),
    % Wait for the slaves to return the computed columns
    % Columns: [{3, [1,1,1,2,2,2,3,3,3]}, {1, [1,2,3,1,2,3,1,2,3]}]
    Columns = wait_for_columns(M, []),
    SortedColumns = lists:sort(fun({Rep1, _}, {Rep2, _}) ->
        Rep1 > Rep2
    end, Columns),
    % ExtractedColumns: [[1,1,1,2,2,2,3,3,3], [1,2,3,1,2,3,1,2,3]]
    ExtractedColumns = lists:map(fun({_, Column}) ->
        Column
    end, SortedColumns),
    Permutations = build_permutations(ExtractedColumns, []),
    print_permutations(Permutations).

init_slaves([], _, _, []) -> ok;
init_slaves([Pid | PidsT], ColumnLen, Elems, [Rep | RepsT]) ->
    Pid ! {init, self(), ColumnLen, Elems, Rep},
    init_slaves(PidsT, ColumnLen, Elems, RepsT).

% @return: [{3, [1,1,1,2,2,2,3,3,3]}, {1, [1,2,3,1,2,3,1,2,3]}]
wait_for_columns(0, Acc) -> Acc;
wait_for_columns(M, Acc) ->
    receive
        {column, Rep, Col} ->  wait_for_columns(M - 1, [{Rep, Col} | Acc])
    end.

% @return: [[1,1], [1,2], [1,3], [2,1], [2,2], [2,3], [3,1], [3,2], [3,3]]
build_permutations([[] | _], Acc) -> lists:reverse(Acc);
build_permutations(Columns, Acc) ->
    Heads = lists:map(fun hd/1, Columns),
    Tails = lists:map(fun tl/1, Columns),
    build_permutations(Tails, [Heads | Acc]).

print_permutations([]) -> ok;
print_permutations([Row | T]) ->
    lists:foreach(fun(Elem) ->
        io:format("~p  ", [Elem])
    end, Row),
    io:format("~n"),
    print_permutations(T).


% c(combinator).
% c(generator).
% combinator:start(2,2).
% combinator:start(2,3).
% combinator:start(3,2).
% combinator:start(3,3).
%
% rm -f *.beam
