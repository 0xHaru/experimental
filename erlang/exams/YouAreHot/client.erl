-module(client).
-export([convert/5]).

convert(from, From, to, To, Temp) ->
    server ! {convert, self(), {from, preprocess(From), to, preprocess(To), Temp}},
    receive
        {result, ConvertedTemp} ->
            % ~s -> print string/atom without quotes
            io:format("~p°~s are equivalent to ~p°~s~n", [Temp, From, ConvertedTemp, To]);
        Any -> io:format("Error: ~p~n", [Any])
    after 2000 ->
        io:format("Client timeout~n")
    end.

preprocess(Scale) ->
    case Scale of
        'C'  -> celsius;
        'F'  -> fahrenheit;
        'K'  -> kelvin;
        'R'  -> rankine;
        'De' -> delisle;
        'N'  -> newton;
        'Re' -> reaumur;
        'Ro' -> romer
    end.


% tempsys:startsys().
% client:convert(from, 'Re', to, 'De', 25).
