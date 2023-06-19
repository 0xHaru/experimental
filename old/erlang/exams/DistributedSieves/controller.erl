-module(controller).
-export([start/1]).

start(NumOfSieves) ->
    {FirstSieve, LastPrime} = sieve:create_ring(NumOfSieves),
    ControllerPid = spawn(fun() -> controller_loop(FirstSieve, LastPrime) end),
    register(controller, ControllerPid),
    io:format("~p - Spawned the controller loop: ~p~n", [self(), ControllerPid]).

controller_loop(FirstSieve, LastPrime) ->
    receive
        {_, quit} ->
            FirstSieve ! quit,
            io:format("~p - Controller shutting down...~n", [self()]),
            exit(quit);
        {ClientPid, is_prime, N} ->
            io:format("~p - Controller received {is_prime, ~p}~n", [self(), N]),
            case math:sqrt(N) > LastPrime of % LastPrime or NumOfSieves?
                true ->
                    ClientPid ! number_too_big;
                false ->
                    FirstSieve ! {is_prime, N},
                    receive
                        {result, Result} -> ClientPid ! {result, Result}
                    end
            end
    end,
    controller_loop(FirstSieve, LastPrime).
