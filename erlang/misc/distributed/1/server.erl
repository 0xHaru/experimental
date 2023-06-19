-module(server).
-export([init/0]).

init() ->
    group_leader(whereis(user), self()),
    io:format("Server is running...~n"),
    server_loop().

server_loop() ->
    receive
        {ClientPid, Msg} ->
            io:format("Echoing received message: ~p~n", [Msg]),
            ClientPid ! {pid, self(), ack, "ACK: message received successfully"},
            server_loop()
    end.

