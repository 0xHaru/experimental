-module(client).
-export([convert/5]).

convert(from, Tmp1, to, Tmp2, M) -> % Richiesta di conversione
     %Pid è il risultato del pattern matching sulla seconda temperatura (C -> Tmp2)
    Pid = case Tmp2 of
        'C' -> spawn(fun() -> tmpConv(fun toC/1) end);
        'F' -> spawn(fun() -> tmpConv(fun toF/1) end);
        'K' -> spawn(fun() -> tmpConv(fun toK/1) end);
        'R' -> spawn(fun() -> tmpConv(fun toR/1) end);
        'De'-> spawn(fun() -> tmpConv(fun toDe/1) end);
        'N' -> spawn(fun() -> tmpConv(fun toN/1) end);
        'Re'-> spawn(fun() -> tmpConv(fun toRe/1) end);
        'Ro'-> spawn(fun() -> tmpConv(fun toRo/1) end);
        X -> io:format("Other is ~p~n", [X]), exit(tempNotFound)
    end,
    Pid ! {convert, self(), Tmp1, M}, % Invio al nodo appena creato la misura attuale e la temperatura di partenza
    receive % Aspetto che mi risponda
        {response,R} -> io:format("~p°~p are equivalent to ~p°~p~n",[M,Tmp1,R,Tmp2])
    end.

tmpConv(Fun) -> % Contiene indirizzo del client e la funzione di conversione da C a Tmp2
    receive
        {convert,Client,TmpFrom,M} -> % Ricevo dal client la richiesta di conversione
            whereis(convertC)!{convC,self(),TmpFrom,M}, % Mando al manager di conversione il mio Pid, la temperatura di partenza e la misura di partenza
            waitResponse(Client,Fun)
    end.


waitResponse(Client,Fun) ->
    receive
        {done,Result} -> Client!{response,Fun(Result)}
    end.

toC(M) -> M.
toF(M) -> (M * 9/5) + 32 .
toK(M) -> M + 273.15 .
toR(M) -> toK(M) * 9/5 .
toDe(M) -> (100 - M) * 3 / 2 .
toN(M) -> M * 33 / 100 .
toRe(M) -> M * 4 / 5 .
toRo(M) -> M * 21 / 40 + 7.5 .
