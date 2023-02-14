% First strategy

-module(ring0).
-export([start/3, loop/0]).

start(NumMsgs, NumProcs, Msg) ->
    io:format("~p - Starting ~p processes...~n", [self(), NumProcs]),
    UnlinkedRing = create_proc([], NumProcs),
    LinkedRing = lists:append(UnlinkedRing, [hd(UnlinkedRing)]),
    io:format("~p - Ring: ~p~n~n", [self(), LinkedRing]),
    send_msg(Msg, NumMsgs, NumMsgs, LinkedRing).

create_proc(Pids, 0) ->
    Pids;

create_proc(Pids, Count) ->
    NewPid = spawn(?MODULE, loop, []),
    io:format("~p - Starting new process ~p~n", [self(), NewPid]),
    create_proc(Pids ++ [NewPid], Count - 1).

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
