-module(midterm).
-export([reverse/1]).

reverse(Str) ->
    MasterPid = self(),
    Half = trunc(length(Str) / 2),
    {FirstHalf, SecondHalf} = lists:split(Half, Str),
    Halves = [FirstHalf] ++ [SecondHalf],
    FinalNode = spawn(fun() -> final_loop(MasterPid, length(Halves), []) end),
    Slaves = spawn_slaves(Halves, FinalNode, 0, []),
    receive
        {result, Result} ->
            Result
    end.

spawn_slaves([], _, _, Pids) -> Pids;
spawn_slaves([Half | T], FinalNode, Id, Pids) ->
    Pid = spawn(fun() -> slave_loop(Id, Half, FinalNode) end),
    spawn_slaves(T, FinalNode, Id + 1, Pids ++ [Pid]).

slave_loop(Id, Half, FinalNode) ->
    Reversed = reverse_list(Half),
    FinalNode ! {reversed, Id, Reversed}.

final_loop(Master, 0, Result) ->
    SortedResult = lists:sort(fun({Id1, _}, {Id2, _}) ->
        Id1 > Id2
    end, Result),
    ListOfStr = lists:map(fun({_, Lst}) -> Lst end, SortedResult),
    ReversedStr = lists:flatten(ListOfStr),
    Master ! {result, ReversedStr};
final_loop(Master, N, Result) ->
    receive
        {reversed, Id, Reversed} ->
            final_loop(Master, N - 1, Result ++ [{Id, Reversed}])
    end.

% Helper functions
reverse_list(Lst) ->
    reverse_list(Lst, []).

reverse_list([], Acc) -> Acc;
reverse_list([H | T], Acc) ->
    reverse_list(T, [H | Acc]).
