-module(client).
-export([start/0, send/1, send2/1]).

start() ->
    {ok, Hostname} = inet:gethostname(),
    net_adm:ping(list_to_atom("server@" ++ Hostname)).

send(Msg) ->
    global:send(server, {self(), Msg}),
    receive
        {ack, Ack} ->
            io:format("~s~n", [Ack])
    after 2000 ->
        io:format("Client timeout~n")
    end.

send2(Msg) ->
    global:whereis_name(server) ! {self(), Msg},
    receive
    {ack, Ack} ->
        io:format("~s~n", [Ack])
    after 2000 ->
        io:format("Client timeout~n")
    end.
