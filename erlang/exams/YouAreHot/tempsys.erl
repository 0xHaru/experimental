-module(tempsys).
-export([startsys/0]).

startsys() ->
    ToCelsiusFunctions = [
        {celsius,    fun(T) -> T end},
        {fahrenheit, fun(T) -> 5/9 * (T - 32) end},
        {kelvin,     fun(T) -> T - 273.15 end},
        {rankine,    fun(T) -> 5/9 * T - 273.15 end},
        {delisle,    fun(T) -> 100 - 2/3 * T end},
        {newton,     fun(T) -> 100/33 * T end},
        {reaumur,    fun(T) -> 5/4 * T end},
        {romer,      fun(T) -> 40/21 * (T - 7.5) end}
    ],
    FromCelsiusFunctions = [
        {celsius,    fun(T) -> T end},
        {fahrenheit, fun(T) -> T * 9/5 + 32 end},
        {kelvin,     fun(T) -> T + 273.15 end},
        {rankine,    fun(T) -> (T + 273.15) * 9/5 end},
        {delisle,    fun(T) -> (100 - T) * 3/2 end},
        {newton,     fun(T) -> T * 33/100 end},
        {reaumur,    fun(T) -> T * 4/5 end},
        {romer,      fun(T) -> T * 21/40 + 7.5 end}
    ],
    FromCelsiusNodes = lists:map(fun({ToScale, Func}) ->
        Pid = spawn(fun() -> from_celsius_loop(ToScale, Func) end),
        {ToScale, Pid}
    end, FromCelsiusFunctions),
    ToCelsiusNodes = lists:map(fun({FromScale, Func}) ->
        Pid = spawn(fun() -> to_celsius_loop(FromScale, Func, FromCelsiusNodes) end),
        {FromScale, Pid}
    end, ToCelsiusFunctions),
    register(server, spawn(fun() -> server_loop(ToCelsiusNodes) end)).


from_celsius_loop(ToScale, Func) ->
    receive
        {convert, Sender, {from, celsius, to, To, CelsiusTemp}} when To =:= ToScale ->
            ConvertedTemp = Func(CelsiusTemp),
            Sender ! {result, ConvertedTemp}
    end,
    from_celsius_loop(ToScale, Func).

to_celsius_loop(FromScale, Func, FromCelsiusNodes) ->
    receive
        {convert, {from, From, to, To, Temp}} when From =:= FromScale ->
            CelsiusTemp = Func(Temp),
            Node = find_node(To, FromCelsiusNodes),
            Node ! {convert, self(), {from, celsius, to, To, CelsiusTemp}},
            receive
                Msg -> server ! Msg
            end
    end,
    to_celsius_loop(FromScale, Func, FromCelsiusNodes).

server_loop(ToCelsiusNodes) ->
    receive
        {convert, ClientPid, {from, From, to, To, Temp}} ->
            Node = find_node(From, ToCelsiusNodes),
            Node ! {convert, {from, From, to, To, Temp}},
            receive
                Msg -> ClientPid ! Msg
            end
    end,
    server_loop(ToCelsiusNodes).

% Utils

find_node([], _) -> error;
find_node(Scale1, [{Scale2, Node} | _]) when Scale1 =:= Scale2 -> Node;
find_node(Scale1, [_ | Tail]) -> find_node(Scale1, Tail).


