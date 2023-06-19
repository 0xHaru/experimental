-module(client).
-export([start/0, stop/0, send_mgs/1]).

% Since I spawn the Server process there is no need for net_adm:ping()
start() ->
    group_leader(whereis(user), self()),
    {ok, Hostname} = inet:gethostname(),
    Server = spawn_link(list_to_atom("server@" ++ Hostname), server, init, []),
    Client = spawn_link(fun() -> client_loop() end),
    global:register_name(client, Client),
    io:format("Server is running on ~p~n", [Hostname]),
    io:format("Nodes: ~p~n", [nodes()]).

client_loop() ->
    receive
        {ack, Response} ->
            io:format("Client received: ~p~n", [Response]),
            client_loop()
    end.

send_mgs(Msg) -> global:send(server, {msg, Msg}).

stop() -> exit(shutdown).
