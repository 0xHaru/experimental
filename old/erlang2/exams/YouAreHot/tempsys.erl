-module(tempsys).
-export([startsys/0]).

startsys() ->
        register(convertC, spawn(fun() -> tmp_conv_init() end)). % Genero Smistatore di richieste

tmp_conv_init() ->
    receive
        {convC,From,Tmp,M} -> % Richiesta di conversione di M Tmp in Celsius
            Pid = case Tmp of
                'C' -> spawn(fun() -> tmpConv(fun fromC/1) end);
                'F' -> spawn(fun() -> tmpConv(fun fromF/1) end);
                'K' -> spawn(fun() -> tmpConv(fun fromK/1) end);
                'R' -> spawn(fun() -> tmpConv(fun fromR/1) end);
                'De'-> spawn(fun() -> tmpConv(fun fromDe/1) end);
                'N' -> spawn(fun() -> tmpConv(fun fromN/1) end);
                'Re'-> spawn(fun() -> tmpConv(fun fromRe/1) end);
                'Ro'-> spawn(fun() -> tmpConv(fun fromRo/1) end);
                X -> io:format("Other is ~p",[X])
            end,
            Pid!{conv,From,M}, % Invio Pid From -> Nodo tmp richiedente i Celsius di M
            tmp_conv_init(); % Torno all'ascolto

        Other -> io:format("I don't like this ~p~n",[Other]),
            tmp_conv_init()
    end.

tmpConv(Fun) -> % Nodo convertitore, riceve messaggio {conv,DestinazioneRisposta,Misura}
    receive
        {conv,From,M} -> From!{done,Fun(M)} % Invia a Destinazione il risultato della conversione da M a Celsius
    end.

fromC(C)   -> C.
fromF(F)   -> (F - 32) * 5 / 9 .
fromK(K)   -> K - 273.15 .
fromR(R)   -> fromK(R * 5 / 9).
fromDe(De) -> - (De * 2 / 3) + 100 .
fromN(N)   -> N * 33 / 100 .
fromRe(Re) -> Re * 5 / 4 .
fromRo(Ro) -> (Ro - 7.5) * 40 / 21 .
