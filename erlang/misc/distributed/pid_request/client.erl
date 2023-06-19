-module(client).
-export([start/0, start2/0, send/1]).

start() ->
    {ok, Hostname} = inet:gethostname(),
    ServerNode = list_to_atom("server@" ++ Hostname),
    Ref = make_ref(),
    {server, ServerNode} ! {ping, self(), Ref},
    receive
        {pong, ServerPid, Ref2} when Ref2 =:= Ref ->
            put(serverPid, ServerPid),
            io:format("Server PID acquired successfully: ~p~n", [ServerPid])
    end.

start2() ->
    {ok, Hostname} = inet:gethostname(),
    ServerNode = list_to_atom("server@" ++ Hostname),
    ServerPid = rpc:call(ServerNode, erlang, whereis, [server]),
    put(serverPid, ServerPid),
    io:format("Server PID acquired successfully~n").

send(Msg) ->
    ServerPid = get(serverPid),
    ServerPid ! {self(), Msg},
    receive
        {pid, Pid, ack, Ack} when Pid =:= ServerPid ->
            io:format("~s~n", [Ack])
    after 2000 ->
        io:format("Client timeout~n")
    end.

