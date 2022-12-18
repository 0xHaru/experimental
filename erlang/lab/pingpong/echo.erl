-module(echo).
-export([start/0, print/1, stop/0]).

start() ->
    ServerPid = spawn(fun () -> server_loop() end),
    register(server, ServerPid),
    io:format("~p - Starting a new server: ~p~n", [self(), ServerPid]).

print(Msg) ->
    server ! {print, Msg}.

stop() ->
    server ! shutdown.

server_loop() ->
    receive
        shutdown ->
            io:format("~p - Server shutting down...~n", [self()]),
            error(shutdown);
        {print, Msg} ->
            io:format("~p - ~p~n", [self(), Msg]),
            server_loop();
        Any ->
            io:format("~p - Invalid messsage: ~p~n", [self(), Any]),
            server_loop()
    end.
