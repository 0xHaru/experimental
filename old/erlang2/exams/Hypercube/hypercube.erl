-module(hypercube).
-export([create/0, hamilton/2, gray/1]).

create() ->
    Labels = [
        "0000", "0001", "0010", "0011",
        "0100", "0101", "0110", "0111",
        "1000", "1001", "1010", "1011",
        "1100", "1101", "1110", "1111"
    ],

    % Spawn the 16 processes and label them
    Nodes = lists:map(fun(Label) ->
        NodePid = spawn(fun() -> node_loop(Label, []) end),
        io:format("The process labeled ~p just started...~n", [Label]),
        {Label, NodePid}
    end, Labels),

    % Link each node to its neighbors
    lists:foreach(fun({_, Node}) ->
        lists:foreach(fun({CandidateLabel, CandidateNeighbor}) ->
            Node ! {connect, CandidateLabel, CandidateNeighbor}
        end, Nodes)
    end, Nodes),

    % Example: [{"0000", <0.90.0>}, {..., ...}, ...]
    [{_, FirstNode} | _] = Nodes,
    register(hypercube, FirstNode),
    register(client, self()).

% Each node has 4 neighbors (each with an hamming distance of 1)
% Example: "0000" -> ["0001", "0010", "0100", "1000"]
node_loop(Label, Neighbors) ->
    receive
        {connect, CandidateLabel, CandidateNeighbor} ->
            UpdatedNeighbors = case hamming_distance(Label, CandidateLabel) of
                1 ->
                    link(CandidateNeighbor),
                    [{CandidateLabel, CandidateNeighbor} | Neighbors];
                _ -> Neighbors
            end,
            node_loop(Label, UpdatedNeighbors);

        {msg, Msg, []} ->
            client ! {msg, {src, Label, Msg}},
            node_loop(Label, Neighbors);

        % Example:
        % 1st - {msg, "Hello",                               ["0001", "0011", ..., "1000"]}
        % 2nd - {msg, {src, "0000", "Hello"},                ["0011", "0010", ..., "1000"]
        % 3rd - {msg, {src, "0001", {src, "0000", "Hello"}}, ["0010", "0110", ..., "1000"]}
        % ...
        {msg, Msg, [NextLabel | Path]} ->
            io:format("{msg, ~p, ~p}~n", [Msg, [NextLabel | Path]]),
            case find_neighbors(NextLabel, Neighbors) of
                none ->
                    client ! {cant_send, Label, Msg};
                {some, {_, Neighbor}} ->
                    Neighbor ! {msg, {src, Label, Msg}, Path}
            end,
            node_loop(Label, Neighbors)
    end.

hamilton(Msg, ["0000" | Path]) ->
    hypercube ! {msg, Msg, Path},
    receive
        {msg, Result} -> io:format("~p~n", [Result]);
        {cant_send, Label, _Path} ->
            io:format("The message couldn't continue after ~p. Traversed path: ~p~n", [Label, _Path]),
            _Path
    end.

% Helper functions

% Example: gray(2) -> ["00","01","11","10"]
gray(0) -> [""];
gray(N) ->
    Gray = gray(N - 1),
    % io:format("~p~n", [Gray]), % DEBUGGING
    ["0" ++ Ch || Ch <- Gray] ++ ["1" ++ Ch || Ch <- lists:reverse(Gray)].

hamming_distance([], []) -> 0;
hamming_distance([E1 | T1], [E2 | T2]) ->
    if
        E1 =:= E2 -> hamming_distance(T1, T2);
        E1 =/= E2 -> 1 + hamming_distance(T1, T2)
    end.

find_neighbors(_, []) -> none;
find_neighbors(Label, [{Label, Neighbor} | _]) -> {some, {Label, Neighbor}};
find_neighbors(NextLabel, [{_, _} | T]) -> find_neighbors(NextLabel, T).

% c(hypercube).
% hypercube:create().
% hypercube:hamilton("Hello", hypercube:gray(4)).
%
% {src,"1000",
%  {src,"1001",
%   {src,"1011",
%    {src,"1010",
%     {src,"1110",
%      {src,"1111",
%       {src,"1101",
%        {src,"1100",
%         {src,"0100",
%          {src,"0101",
%           {src,"0111",
%            {src,"0110",
%             {src,"0010",
%              {src,"0011",{src,"0001",{src,"0000","Hello"}}}}}}}}}}}}}}}}

% Note: the hypercube can be seen as a graph with 16 vertices each with 4 edges

% Links:
%   - https://en.wikipedia.org/wiki/Hamiltonian_path
%   - https://en.wikipedia.org/wiki/Hamming_distance
