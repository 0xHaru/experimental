-module(client).
-export([is_prime/1, quit/0]).
-define(CONTROLLER_HOST, 'controller@lab').

is_prime(N) ->
    {controller, ?CONTROLLER_HOST} ! {is_prime, self(), N},
    receive
        number_too_big ->
            io:format("~p - ~p is too big!~n", [self(), N]);
        {result, Result} ->
            case Result of
                true -> io:format("~p - ~p is prime~n", [self(), N]);
                false -> io:format("~p - ~p is NOT prime~n", [self(), N])
            end
    after 5000 ->
        io:format("~p - Timeout~n", [self()])
    end.

quit() -> {controller, ?CONTROLLER_HOST} ! quit.
