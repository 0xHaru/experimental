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

    % Link each node to its neighbours
    lists:foreach(fun({_, Node}) ->
        lists:foreach(fun({CandidateLabel, CandidateNeighbour}) ->
            Node ! {connect, CandidateLabel, CandidateNeighbour}
        end, Nodes)
    end, Nodes),

    % Example: [{"0000", <0.90.0>}, {..., ...}, ...]
    [{_, FirstNode} | _] = Nodes,
    register(hypercube, FirstNode),
    register(client, self()).


node_loop(Label, Neighbours) ->
    receive
        {connect, CandidateLabel, CandidateNeighbour} ->
            UpdatedNeighbours = case hamming_distance(Label, CandidateLabel) of
                1 ->
                    link(CandidateNeighbour),
                    [{CandidateLabel, CandidateNeighbour} | Neighbours];
                _ -> Neighbours
            end,
            node_loop(Label, UpdatedNeighbours);

        {msg, Msg, []} ->
            client ! {msg, {src, Label, Msg}},
            node_loop(Label, Neighbours);

        {msg, Msg, [NextLabel | Path]} ->
            case find_neighbours(NextLabel, Neighbours) of
                none ->
                    client ! {cant_send, Label, Msg};
                {some, {_, Neighbour}} ->
                    Neighbour ! {msg, {src, Label, Msg}, Path}
            end,
            node_loop(Label, Neighbours)
    end.

hamilton(Msg, ["0000" | Path]) ->
    hypercube ! {msg, Msg, Path},
    receive
        {msg, X} -> X;
        {cant_send, Label, _Path} ->
            io:format("The message couldn't continue after ~p. Traversed path: ~p~n", [Label, _Path]),
            _Path
    end.

% Helper functions
gray(0) -> [""];
gray(N) ->
    Gray = gray(N - 1),
    % io:format("~p~n", [Gray]), % DEBUGGING
    ["0" ++ Ch || Ch <- Gray] ++ ["1" ++ Ch || Ch <- lists:reverse(Gray)].

hamming_distance([], []) -> 0;
hamming_distance([X|A], [Y|B]) ->
    if
        X =:= Y -> hamming_distance(A, B);
        X =/= Y -> 1 + hamming_distance(A, B)
    end.

find_neighbours(_, []) -> none;
find_neighbours(Label, [{Label, Neighbour} | _]) -> {some, {Label, Neighbour}};
find_neighbours(NextLabel, [{_, _} | T]) -> find_neighbours(NextLabel, T).
