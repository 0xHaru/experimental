-module(sieve).
-export([create_ring/1, list_primes/1]).

create_ring(NumOfSieves) ->
    Primes = list_primes(NumOfSieves),
    LastPrime = hd(lists:reverse(Primes)),

    Pids = spawn_sieves(NumOfSieves, []),
    FirstSieve = hd(Pids),
    register(first_sieve, FirstSieve),

    lists:foreach(fun({From, To, PrimeId}) ->
        From ! {init, To, PrimeId}
    end, lists:zip3(Pids, tl(Pids) ++ [FirstSieve], Primes)),

    io:format("~p - Primes: ~p~n", [self(), Primes]),
    io:format("~p - Sieves PIDs: ~p~n", [self(), Pids]),

    {FirstSieve, LastPrime}.

spawn_sieves(0, Pids) -> Pids;
spawn_sieves(Count, Pids) ->
    NewPid = spawn(fun() -> sieve_init() end),
    spawn_sieves(Count - 1, Pids ++ [NewPid]).

sieve_init() ->
    receive
        {init, NextSieve, PrimeId} ->
            link(NextSieve), % When the first sieve receives a quit message all the other sieves will die
            sieve_loop(NextSieve, PrimeId)
    end.

sieve_loop(NextSieve, PrimeId) ->
    io:format("~p - NextSieve: ~p  PrimeId: ~p~n", [self(), NextSieve, PrimeId]),
    receive
        quit ->
            NextSieve ! quit, % Kinda redundant since they are already linked
            exit(quit);
        {is_prime, N} ->
            RootOfN = math:sqrt(N),
            if
                N =:= 0 orelse N =:= 1 -> first_sieve ! {result, false};
                PrimeId > RootOfN -> first_sieve ! {result, true};
                N rem PrimeId =:= 0 -> first_sieve ! {result, false};
                true -> NextSieve ! {is_prime, N} % Pass the message to the next sieve
            end;
        {result, Result} -> % First sieve
            controller ! {result, Result}
    end,
    sieve_loop(NextSieve, PrimeId).

% Helper functions
is_prime(PrimesSoFar, Candidate) -> not lists:any(fun(X) -> Candidate rem X =:= 0 end, PrimesSoFar).

list_primes(N, PrimesSoFar, _) when (length(PrimesSoFar) >= N) -> lists:reverse(PrimesSoFar);

list_primes(N, PrimesSoFar, Candidate) ->
        case is_prime(PrimesSoFar, Candidate) of
            true -> list_primes(N, [Candidate | PrimesSoFar], Candidate + 2);
            false -> list_primes(N, PrimesSoFar, Candidate + 2)
        end.

list_primes(N) when N < 2 -> [];
list_primes(2) -> [2];
list_primes(N) -> list_primes(N, [2], 3).
