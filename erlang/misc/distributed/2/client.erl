-module(client).
-export([start/0, send/1]).

start() ->
    {ok, Hostname} = inet:gethostname(),
    put(serverNode, list_to_atom("server@" ++ Hostname)),
    ok.

send(Msg) ->
    ServerNode = get(serverNode),
    {server, ServerNode} ! {self(), Msg},
    receive
        {ack, Ack} ->
            io:format("~s~n", [Ack])
    after 2000 ->
        io:format("Client timeout~n")
    end.

