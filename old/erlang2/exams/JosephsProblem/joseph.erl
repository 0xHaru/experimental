-module(joseph).
-export([joseph/2]).

joseph(N, K) ->
    % Spawn the N hebrews
    Pids = [spawn(hebrew, start, [Id, K]) || Id <- lists:seq(1, N)],
    ZippedPids = lists:zip(Pids, tl(Pids) ++ [hd(Pids)]),
    % Initialize them
    [Curr ! {next, Next, master, self()} || {Curr, Next} <- ZippedPids],
    hd(Pids) ! {from, lists:last(Pids), alive, N, k, 1},
    % Wait for the survivor to notify you
    io:format("In a circle of ~p people, killing number ~p~n", [N, K]),
    receive
        {done, from, _, id, Id} ->
            io:format("Joseph is the Hebrew in position ~p~n", [Id]);
        Any ->
            io:format("Error: ~p~n", [Any])
    end.

% c(test).
% c(hebrew).
% c(joseph).
% joseph:joseph(6, 2). -> 5
% test:test().
%
% rm -f *.beam
