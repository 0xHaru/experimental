% Second strategy

-module(ring2).
-export([start/3, loop/0]).

start(NumMsgs, NumProcs, Msg) ->
    io:format("~p - Starting ~p processes...~n", [self(), NumProcs]),
    _ = create_proc(NumProcs),
    Ring = receive
        {done, [_ | PidsT]} ->
            PidsT ++ [hd(PidsT)]
    end,
    io:format("~p - Ring: ~p~n~n", [self(), Ring]),
    send_msg(Msg, NumMsgs, NumMsgs, Ring).

create_proc(Count) ->
    FirstPid = spawn(?MODULE, loop, []),
    FirstPid ! {create, Count - 1, [self()]},
    io:format("~p - Starting new process ~p~n", [self(), FirstPid]).

send_msg(_, 0, _, [PidsH | PidsT]) ->
    io:format("~p - Sending STOP signal to ~p~n", [self(), PidsH]),
    PidsH ! {stop, PidsT};

send_msg(Msg, Count, TotMsgs, [PidsH | PidsT]) ->
    MsgNum = TotMsgs - Count + 1,
    io:format("~p - Sending message ~p (~p) to ~p~n", [self(), Msg, MsgNum, PidsH]),
    PidsH ! {Msg, MsgNum, PidsT},
    send_msg(Msg, Count - 1, TotMsgs, [PidsH | PidsT]).

loop() ->
    receive
        {create, 0, [FirstPid | PidsT]} ->
            Pids =  [FirstPid | PidsT],
            FirstPid ! {done, Pids ++ [self()]},
            loop();
        {create, Count, Pids} ->
            NewPid = spawn(?MODULE, loop, []),
            io:format("~p - Starting new process ~p~n", [self(), NewPid]),
            NewPid ! {create, Count - 1, Pids ++ [self()]},
            loop();
        {stop, [PidsH | PidsT]} ->
            io:format("~p - Relaying STOP signal to ~p~n", [self(), PidsH]),
            PidsH ! {stop, PidsT};
        {Msg, MsgNum, [PidsH | PidsT]} ->
            io:format("~p - Relaying message ~p (~p) to ~p~n", [self(), Msg, MsgNum, PidsH]),
            PidsH ! {Msg, MsgNum, PidsT},
            loop()
    end.

% Notes:
%   ?MODULE is a macro that expands to "ring1"
