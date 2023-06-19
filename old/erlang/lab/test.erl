-module(fuck).
-export([split_string/1]).

split_string([], _, _, _, _, Chunks) -> lists:reverse(Chunks);
split_string(Str, StrLen, ChunkLen1, ChunkLen2, ChunkLim, Chunks) ->
    io:format("~nChunks: ~p~n", [Chunks]),
    io:format("lenght(Chunks): ~p~n", [length(Chunks)]),
    io:format("ChunkLim: ~p~n", [ChunkLim]),
    io:format("length(Chunks) >= ChunkLim: ~p~n", [length(Chunks) >= ChunkLim]),
    Tmp = length(Chunks) >= ChunkLim,
    case Tmp of
        true ->
            {Chunk, T} = lists:split(ChunkLen2, Str),
            split_string(T, StrLen - ChunkLen2, ChunkLen1, ChunkLen2, ChunkLim, [Chunk | Chunks]);
        false ->
            {Chunk, T} = lists:split(ChunkLen1, Str),
            split_string(T, StrLen - ChunkLen1, ChunkLen1, ChunkLen1, ChunkLim, [Chunk | Chunks]);
        Any ->
            io:format("FUCK: ~p~n", [Any])
    end.
