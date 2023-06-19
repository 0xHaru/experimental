-module(server).
-export([init/0]).

init() ->
    group_leader(whereis(user), self()),
    io:format("Running...~n"),
    global:register_name(server, self()),
    server_loop().

server_loop() ->
    receive
        {msg, Msg} ->
            io:format("Server received: ~p~n", [Msg]),
            global:send(client, {ack, string:uppercase(Msg)}), % BROKEN
            server_loop()
    end.
