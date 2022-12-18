-module(drs).
-export([spawn_master/0, reverse_string/2]).

spawn_master() ->
    MasterPid = spawn(fun() -> master_loop() end),
    register(master, MasterPid),
    io:format("~p - Spawned the master process: ~p | [CLIENT]~n", [self(), MasterPid]).

reverse_string(Str, NumDiv) ->
    master ! {self(), reverse, Str, NumDiv},
    MasterPid = whereis(master),
    receive
        {MasterPid, ReversedStr} -> ReversedStr
    end.

split_string(Str, NumDiv) ->
    StrLen = length(Str),
    ChunkLen1 = StrLen div NumDiv + 1,
    ChunkLen2 = StrLen div NumDiv,
    ChunkLim = StrLen rem NumDiv,
    split_string(Str, [], {ChunkLen1, ChunkLen2, ChunkLim}).

split_string([], Chunks, _) -> lists:reverse(Chunks);
split_string(Str, Chunks, {ChunkLen1, ChunkLen2, ChunkLim}) ->
    case length(Chunks) >= ChunkLim of
        true ->
            {Chunk, T} = lists:split(ChunkLen2, Str),
            split_string(T, [Chunk | Chunks], {ChunkLen1, ChunkLen2, ChunkLim});
        false ->
            {Chunk, T} = lists:split(ChunkLen1, Str),
            split_string(T, [Chunk | Chunks], {ChunkLen1, ChunkLen2, ChunkLim})
    end.

slave(Id) ->
    MasterPid = whereis(master),
    receive
        {reverse, MasterPid, Str} ->
            io:format("~p - Reversing this chunk: ~p | [SLAVE]~n", [self(), Str]),
            master ! {reverse, Id, string:reverse(Str)},
            slave(Id)
    end.

master_loop() ->
    receive
        {ClientPid, reverse, Str, NumDiv} ->
            SplitStr = split_string(Str, NumDiv),
            EnumSplitStr = lists:enumerate(SplitStr),

            SlavePids = lists:map(fun ({Index, String}) ->
                SlavePid = spawn(fun () -> slave(Index) end),
                SlavePid ! {reverse, self(), String},
                SlavePid
            end, EnumSplitStr),
            io:format("~p - Slaves: ~p | [MASTER]~n", [self(), SlavePids]),

            % Receive all the responses
            Responses = receive_responses(length(SplitStr), []),

            % Sort the responses based on their id
            SortedResponses = lists:sort(fun ({Id1, _}, {Id2, _}) ->
                Id2 > Id1
            end, Responses),

            io:format("~p - SortedResponses: ~p | [MASTER]~n", [self(), SortedResponses]),

            ReversedStr = lists:foldl(fun ({_, String}, Acc) ->
                String ++ Acc
            end, "", SortedResponses),

            ClientPid ! {self(), ReversedStr},

            master_loop()
    end.

receive_responses(0, Responses) -> Responses;
receive_responses(HowManyLeft, Responses) ->
    receive
        {reverse, Id, Str} ->
            receive_responses(HowManyLeft - 1, [{Id, Str} | Responses]);
        Any -> io:format("weird message in receive_responses[~p]~n", [Any])
    end.


% Refs vs whereis(master) - email prof?
