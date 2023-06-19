-module(client).
-export([start/0, send/1]).

start() ->
    {ok, Hostname} = inet:gethostname(),
    ServerPid = spawn(list_to_atom("server@" ++ Hostname), server, init, []),
    put(serverPid, ServerPid),
    ok.

send(Msg) ->
    ServerPid = get(serverPid),
    ServerPid ! {self(), Msg},
    receive
        {pid, Pid, ack, Ack} when Pid =:= ServerPid ->
            io:format("~s~n", [Ack])
    after 2000 ->
        io:format("Client timeout~n")
    end.

