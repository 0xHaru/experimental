-module(server).
-export([init/0]).

init() ->
    group_leader(whereis(user), self()),
    io:format("Server is running...~n"),
    server_loop(0, 0, [], []).

server_loop(Index1, Index2, Acc1, Acc2) ->
    receive
        {mm1, {_, Size, Lst, E} = Msg} when Index1 =:= Size - 1, Index2 =:= Size ->
            Reversed = concat(length(Lst), [E | Acc1], Acc2),
            io:format("Received ~p from mm1~n", [Msg]),
            io:format("The reverse of ~p is ~p~n", [Lst, Reversed]),
            server_loop(0, 0, [], []);
        {mm2, {_, Size, Lst, E} = Msg} when Index1 =:= Size, Index2 =:= Size - 1 ->
            Reversed = concat(length(Lst), Acc1, [E | Acc2]),
            io:format("Received ~p from mm2~n", [Msg]),
            io:format("The reverse of ~p is ~p~n", [Lst, Reversed]),
            server_loop(0, 0, [], []);
        {mm1, {Index, _, _, E} = Msg} ->
            io:format("Received ~p from mm1~n", [Msg]),
            server_loop(Index + 1, Index2, [E | Acc1], Acc2);
        {mm2, {Index, _, _, E} = Msg} ->
            io:format("Received ~p from mm2~n", [Msg]),
            server_loop(Index1, Index + 1, Acc1, [E | Acc2])
    end.


concat(Len, L1, L2) when Len rem 2 =:= 0 -> L2 ++ L1;
concat(_, [ _ | T1 ], L2) -> L2 ++ T1.

% Q&A:
%
% Q: Why Size and Size - 1 at lines 11 and 16?
% A: Either mm1 or mm2 will send its last message before the other one terminated,
%    this means that one of the indexes will be increased one too many times.
%    I would also like to highlight how the two lines will never both be executed.
%
% Q: Why Index and not Index1 or Index2 at lines 21 and 24?
% A: I'm honestly not sure if I should try to pattern match on the current indexes
%    to guarantee the receiving order or not, so far it has been working well though.
%
% Notes:
%
% In the guards ; is equal to an OR (||) and , is equal to an AND (&&)
