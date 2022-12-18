-module(client).
-export([create/0, exit/0]).

create() ->
    ClientPid = spawn(fun () -> client_loop() end),
    register(client, ClientPid),
    io:format("~p - Creating a new client: ~p~n", [self(), ClientPid]).

exit() ->
    client ! shutdown.

client_loop() ->
    ServerPid = whereis(server),
    link(ServerPid),
    io:format("~p - Client (~p) linked to the server (~p)~n", [self(), self(), ServerPid]),
    receive
        shutdown ->
            io:format("~p - Client shutting down...~n", [self()]);
        Any ->
            io:format("~p - Client received: ~p~n", [self(), Any]),
            client_loop()
    end.

% echo:start().
% echo:print("This is a test!").
% client:create().
% client ! "This is a test!".
% regs().
% echo:stop().
% regs().
