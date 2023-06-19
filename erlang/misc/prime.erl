-module(prime).

-export([generate_primes/1, is_prime/1]).

% List the first N prime numbers
generate_primes(N) ->
    generate_primes(N - 1, [2]).

generate_primes(0, Acc) ->
    lists:reverse(Acc);
generate_primes(N, [LatestPrime | _] = Acc) ->
    NextPrime = find_next_prime(LatestPrime + 1),
    generate_primes(N - 1, [NextPrime | Acc]).

find_next_prime(N) ->
    case is_prime(N) of
        true ->
            N;
        false ->
            find_next_prime(N + 1)
    end.

is_prime(N) ->
    not lists:any(fun(X) -> N rem X =:= 0 end, lists:seq(2, trunc(math:sqrt(N)))).

