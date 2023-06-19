-module(client).
-export([start/0, close/0, do_reverse/1]).

start() ->
    group_leader(whereis(user), self()),
    {ok, Hostname} = inet:gethostname(),
    Server = spawn_link(list_to_atom("server@" ++ Hostname), server, init, []),
    MM1    = spawn_link(list_to_atom("mm1@" ++ Hostname), mm, init, [mm1, Server]),
    MM2    = spawn_link(list_to_atom("mm2@" ++ Hostname), mm, init, [mm2, Server]),
    Client = spawn_link(fun() -> client_loop(MM1, MM2) end),
    register(client, Client),
    io:format("Server is running on ~p~n", [Hostname]),
    io:format("Nodes: ~p~n", [nodes()]).

% Shut everything down by killing the client that spawn_linked all the other processes
close() ->
    io:format("Shutting down...~n"),
    exit(shutdown).

client_loop(MM1, MM2) ->
    receive
        {Size, Lst, FirstHalf, SecondHalf} ->
            forward(MM1, MM2, 0, Size, Lst, FirstHalf, SecondHalf),
            client_loop(MM1, MM2)
    end.

forward(MM1, MM2, Index, Size, Lst, [E1], [E2]) ->
    MM1 ! {Index, Size, Lst, E1},
    MM2 ! {Index, Size, Lst, E2};
forward(MM1, MM2, Index, Size, Lst, [H1 | T1], [H2 | T2]) ->
    MM1 ! {Index, Size, Lst, H1},
    MM2 ! {Index, Size, Lst, H2},
    forward(MM1, MM2, Index + 1, Size, Lst, T1, T2).

do_reverse(Lst) ->
    case length(Lst) rem 2 =:= 0 of
        true ->
            Size = trunc(length(Lst) / 2),
            FirstHalf = lists:sublist(Lst, Size),
            SecondHalf = lists:sublist(Lst, Size + 1, Size),
            client ! {Size, Lst, FirstHalf, SecondHalf};
        false ->
            Size = trunc(length(Lst) / 2) + 1,
            FirstHalf = lists:sublist(Lst, Size),
            SecondHalf = lists:sublist(Lst, Size, Size),
            client ! {Size, Lst, FirstHalf, SecondHalf}
    end.
